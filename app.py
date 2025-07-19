from flask import Flask, request, jsonify, send_from_directory, url_for, redirect
from moviepy.editor import (
    ImageClip, concatenate_videoclips, AudioFileClip, CompositeAudioClip,
    TextClip, CompositeVideoClip
)
import os
import random
import shutil
import uuid
import logging
import requests
import jwt
import mysql.connector
import hashlib
import hmac
import json
from werkzeug.utils import secure_filename
from datetime import datetime, timedelta, timezone
from functools import wraps
from flask_cors import CORS
from dotenv import load_dotenv
from werkzeug.security import generate_password_hash
import smtplib
from email.message import EmailMessage


app = Flask(__name__)
CORS(app, resources={r"/*": {"origins": "*"}})

# Load environment variables
env_path = os.path.abspath(os.path.join(os.path.dirname(__file__), '.env'))
load_dotenv(dotenv_path=env_path)

# Configuration from environment variables
frontend_url = os.getenv('NEXT_PUBLIC_API_URL')
RESET_TOKEN_EXPIRY_HOURS = int(os.getenv('RESET_TOKEN_EXPIRY_HOURS', 1))
MAX_VIDEOS_PER_USER = int(os.getenv('MAX_VIDEOS_PER_USER', 10))  # Maximum number of videos a user can have

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)
app.logger.handlers.clear()
app.logger.addHandler(logging.StreamHandler())

# App configuration
app.config['SECRET_KEY'] = os.getenv('JWT_SECRET_KEY')
app.config['JWT_EXPIRATION'] = int(os.getenv('JWT_EXPIRATION', 86400))
app.config['MAX_CONTENT_LENGTH'] = int(os.getenv('MAX_CONTENT_LENGTH', 33554432))  # 32MB max upload size

# Cashfree configuration
CASHFREE_APP_ID = os.getenv('CASHFREE_APP_ID')
CASHFREE_SECRET_KEY = os.getenv('CASHFREE_SECRET_KEY')
CASHFREE_BASE_URL = os.getenv('CASHFREE_BASE_URL')

# Define paths for media
IMAGE_FOLDER = os.getenv('IMAGE_FOLDER', 'media/images')
VOICE_FOLDER = os.getenv('VOICE_FOLDER', 'media/voice')
BACKGROUND_FOLDER = os.getenv('BACKGROUND_FOLDER', 'media/background')
OUTPUT_BASE_FOLDER = os.getenv('OUTPUT_BASE_FOLDER', 'new_output')

# Database configuration
DATABASE_CONFIG = {
    "host": os.getenv('DB_HOST'),
    "user": os.getenv('DB_USER'),
    "password": os.getenv('DB_PASSWORD'),
    "database": os.getenv('DB_NAME'),
    "auth_plugin": os.getenv('DB_AUTH_PLUGIN')
}

# Ensure all required folders exist
for folder in [IMAGE_FOLDER, VOICE_FOLDER, BACKGROUND_FOLDER, OUTPUT_BASE_FOLDER]:
    os.makedirs(folder, exist_ok=True)

# Helper functions
def get_db_connection():
    try:
        connection = mysql.connector.connect(**DATABASE_CONFIG)
        return connection
    except Exception as e:
        logger.error(f"Database connection error: {e}")
        return None

# Fixed token_required decorator - separate authentication from subscription validation
def token_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        token = None
        if 'Authorization' in request.headers:
            token = request.headers['Authorization'].split(" ")[1]
        
        if not token:
            return jsonify({'message': 'Token is missing'}), 401
        
        try:
            data = jwt.decode(token, app.config['SECRET_KEY'], algorithms=["HS256"])
            
            conn = get_db_connection()
            cursor = conn.cursor(dictionary=True)
            cursor.execute("SELECT * FROM users WHERE id = %s", (data['user_id'],))
            current_user = cursor.fetchone()
            cursor.close()
            conn.close()
            
            if not current_user:
                return jsonify({'message': 'Invalid token'}), 401

            # Don't block access based on subscription - just pass user data
            # Subscription validation should be done per endpoint as needed
                
        except Exception as e:
            return jsonify({'message': 'Invalid token'}), 401
        
        return f(current_user, *args, **kwargs)
    
    return decorated

# New decorator specifically for subscription-required endpoints
def subscription_required(f):
    @wraps(f)
    def decorated(*args, **kwargs):
        # First check if user is authenticated
        token = None
        if 'Authorization' in request.headers:
            token = request.headers['Authorization'].split(" ")[1]
        
        if not token:
            return jsonify({'message': 'Token is missing'}), 401
        
        try:
            data = jwt.decode(token, app.config['SECRET_KEY'], algorithms=["HS256"])
            
            conn = get_db_connection()
            cursor = conn.cursor(dictionary=True)
            cursor.execute("SELECT * FROM users WHERE id = %s", (data['user_id'],))
            current_user = cursor.fetchone()
            cursor.close()
            conn.close()
            
            if not current_user:
                return jsonify({'message': 'Invalid token'}), 401

            # Check subscription status only for subscription-required endpoints
            if current_user['subscription_expiry']:
                expiry_date = datetime.strptime(str(current_user['subscription_expiry']), '%Y-%m-%d').date()
                if expiry_date < datetime.now().date():
                    return jsonify({
                        'message': 'Subscription expired', 
                        'subscription_expired': True,
                        'subscription_expiry': str(current_user['subscription_expiry'])
                    }), 403
                
        except Exception as e:
            return jsonify({'message': 'Invalid token'}), 401
        
        return f(current_user, *args, **kwargs)
    
    return decorated

def get_user_output_folder(user_id):
    """Generate and ensure existence of user-specific output folder"""
    user_folder = os.path.join(OUTPUT_BASE_FOLDER, f"user_{user_id}")
    os.makedirs(user_folder, exist_ok=True)
    return user_folder

def get_random_duration(min_time, max_time):
    return random.uniform(min_time, max_time)

def apply_transition_effects(clip1, clip2, transition_type, duration):
    if transition_type == "fade":
        return clip1.fadeout(duration), clip2.fadein(duration)
    elif transition_type == "slide":
        return clip1.set_start(clip1.end), clip2.set_start(clip1.end + duration)
    return clip1, clip2

def clear_folder(folder_path):
    try:
        if os.path.exists(folder_path):
            for filename in os.listdir(folder_path):
                file_path = os.path.join(folder_path, filename)
                if os.path.isfile(file_path):
                    os.unlink(file_path)
        return True
    except Exception as e:
        logger.error(f"Error clearing folder {folder_path}: {e}")
        return False

def generate_unique_filename():
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    random_suffix = ''.join(random.choices('0123456789', k=4))
    return f"video_{timestamp}_{random_suffix}.mp4"

def generate_order_id():
    return f"order_{str(uuid.uuid4())[:8]}"

def update_subscription_status(user_id, subscription_type, duration_days):
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        
        # Calculate new expiry date
        new_expiry = datetime.now() + timedelta(days=duration_days)
        
        cursor.execute(
            """UPDATE users 
            SET subscription = %s, subscription_expiry = %s 
            WHERE id = %s""",
            (subscription_type, new_expiry.date(), user_id)
        )
        
        conn.commit()
        cursor.close()
        conn.close()
        return True
    except Exception as e:
        logger.error(f"Error updating subscription: {e}")
        return False

def save_video_record(user_id, filename, duration):
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        
        cursor.execute("""
            INSERT INTO videos (
                user_id, filename, duration, created_at
            ) VALUES (%s, %s, %s, %s)
        """, (
            user_id,
            filename,
            duration,
            datetime.now()
        ))
        
        conn.commit()
        cursor.close()
        conn.close()
        return True
    except Exception as e:
        logger.error(f"Error saving video record: {e}")
        return False

def save_payment_record(order_id, user_id, amount, payment_details):
    try:
        conn = get_db_connection()
        cursor = conn.cursor()
        
        cursor.execute("""
            INSERT INTO payments (
                order_id, cf_order_id, user_id, amount, payment_status, 
                payment_method, transaction_id, payment_date
            ) VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
        """, (
            order_id,
            payment_details.get('cf_order_id'),
            user_id,
            amount,
            payment_details.get('order_status'),
            payment_details.get('payment_method'),
            payment_details.get('cf_payment_id'),
            datetime.now()
        ))
        
        conn.commit()
        cursor.close()
        conn.close()
        return True
    except Exception as e:
        logger.error(f"Error saving payment record: {e}")
        return False

def verify_payment_status(order_id):
    try:
        headers = {
            "x-client-id": CASHFREE_APP_ID,
            "x-client-secret": CASHFREE_SECRET_KEY,
            "x-api-version": "2022-09-01"
        }
        
        response = requests.get(
            f"{CASHFREE_BASE_URL}/orders/{order_id}",
            headers=headers
        )
        
        if response.status_code == 200:
            payment_details = response.json()
            is_paid = (payment_details.get('order_status') == "PAID" and 
                      payment_details.get('payment_status') == "SUCCESS")
            return is_paid, payment_details
        return False, None
    except Exception as e:
        logger.error(f"Error verifying payment: {str(e)}")
        return False, None

def get_user_video_count(user_id):
    """Get the number of videos created by a user"""
    try:
        conn = get_db_connection()
        cursor = conn.cursor(dictionary=True)
        cursor.execute("SELECT COUNT(*) as count FROM videos WHERE user_id = %s", (user_id,))
        result = cursor.fetchone()
        cursor.close()
        conn.close()
        return result['count']
    except Exception as e:
        logger.error(f"Error getting user video count: {e}")
        return 0

# Email sending function
def send_email(to_email, subject, body):
    try:
        msg = EmailMessage()
        msg.set_content(body)
        msg['Subject'] = subject
        msg['From'] = os.getenv('SMTP_FROM')
        msg['To'] = to_email
        
        # Connect to SMTP server and send
        server = smtplib.SMTP(os.getenv('SMTP_HOST'), int(os.getenv('SMTP_PORT')))
        server.starttls()
        server.login(os.getenv('SMTP_USER'), os.getenv('SMTP_PASSWORD'))
        server.send_message(msg)
        server.quit()
        return True
    except Exception as e:
        logger.error(f"Error sending email: {e}")
        return False
    

# Routes

@app.route("/clear_cache", methods=["POST"])
@token_required
def clear_cache_route(current_user):
    try:
        user_folder = get_user_output_folder(current_user['id'])
        success = clear_folder(user_folder)
        
        # Also clear database records
        conn = get_db_connection()
        cursor = conn.cursor()
        cursor.execute("DELETE FROM videos WHERE user_id = %s", (current_user['id'],))
        conn.commit()
        cursor.close()
        conn.close()
        
        if success:
            return jsonify({"message": "Cache cleared successfully"}), 200
        return jsonify({"error": "Failed to clear cache"}), 500
    except Exception as e:
        logger.error(f"Error in clear_cache_route: {e}")
        return jsonify({"error": str(e)}), 500

@app.route("/delete_video", methods=["DELETE"])
@token_required
def delete_video(current_user):
    try:
        data = request.get_json()
        video_id = data.get("videoId")
        filename = data.get("filename")

        if not video_id and not filename:
            logger.error("Either Video ID or Filename is required")
            return jsonify({"error": "Video ID or Filename is required"}), 400

        # Check if video belongs to the user
        conn = get_db_connection()
        cursor = conn.cursor(dictionary=True)

        if video_id:
            cursor.execute("SELECT * FROM videos WHERE filename = %s AND user_id = %s", (video_id, current_user['id']))
        else:
            cursor.execute("SELECT * FROM videos WHERE filename = %s AND user_id = %s", (filename, current_user['id']))

        video = cursor.fetchone()
        
        if not video:
            return jsonify({"error": "Video not found or unauthorized"}), 404

        user_folder = get_user_output_folder(current_user['id'])
        video_path = os.path.join(user_folder, video['filename'])  # Always use filename from DB

        if not os.path.exists(video_path):
            logger.error(f"Video not found at path: {video_path}")
            return jsonify({"error": "Video not found"}), 404

        try:
            os.remove(video_path)
            # Delete from database
            if video_id:
                cursor.execute("DELETE FROM videos WHERE filename = %s", (video_id,))
            else:
                cursor.execute("DELETE FROM videos WHERE filename = %s", (filename,))
                
            conn.commit()
            return jsonify({"message": "Video deleted successfully"}), 200
        except OSError as e:
            logger.error(f"Error deleting video {video['filename']}: {e}")
            return jsonify({"error": f"Failed to delete video: {str(e)}"}), 500
    except Exception as e:
        logger.error(f"Unexpected error in delete_video: {e}")
        return jsonify({"error": str(e)}), 500
    finally:
        cursor.close()
        conn.close()

@app.route('/get_videos', methods=['GET'])
@token_required
def get_videos(current_user):
    try:
        page = max(1, int(request.args.get('page', 1)))
        limit = max(1, int(request.args.get('limit', 6)))

        conn = get_db_connection()
        cursor = conn.cursor(dictionary=True)
        
        # Get total count
        cursor.execute("""
            SELECT COUNT(*) as total 
            FROM videos 
            WHERE user_id = %s
        """, (current_user['id'],))
        total = cursor.fetchone()['total']

        # Get paginated videos
        cursor.execute("""
            SELECT * FROM videos 
            WHERE user_id = %s 
            ORDER BY created_at DESC 
            LIMIT %s OFFSET %s
        """, (current_user['id'], limit, (page - 1) * limit))
        
        videos = []
        for video in cursor.fetchall():
            videos.append({
                "videoId": video['filename'],
                "title": os.path.splitext(video['filename'])[0],
                "url": f"/video/{video['filename']}",
                "createdAt": video['created_at'].isoformat(),
                "duration": video['duration']
            })

        cursor.close()
        conn.close()

        return jsonify({
            "videos": videos,
            "hasMore": total > (page * limit),
            "total": total
        })

    except Exception as e:
        logger.error(f"Error in get_videos: {e}")
        return jsonify({"error": str(e)}), 500

@app.route("/video/<filename>")
def serve_video(filename):
    try:
        # Extract user ID from filename or query DB to find the owner
        conn = get_db_connection()
        cursor = conn.cursor(dictionary=True)
        cursor.execute("""
            SELECT user_id FROM videos 
            WHERE filename = %s
        """, (filename,))
        video = cursor.fetchone()
        
        if not video:
            return jsonify({"error": "Video not found"}), 404
            
        user_id = video['user_id']
        cursor.close()
        conn.close()
        
        # Generate the appropriate user folder path
        user_folder = os.path.join(OUTPUT_BASE_FOLDER, f"user_{user_id}")
        
        # Serve the video from the correct user folder
        return send_from_directory(
            user_folder,
            filename,
            as_attachment=False,
            mimetype='video/mp4'
        )
    except Exception as e:
        logger.error(f"Error serving video {filename}: {e}")
        return jsonify({"error": str(e)}), 404

@app.route("/check_video_limit", methods=["GET"])
@token_required
def check_video_limit(current_user):
    """Check if the user has reached their video limit"""
    try:
        count = get_user_video_count(current_user['id'])
        return jsonify({
            "count": count,
            "limit": MAX_VIDEOS_PER_USER,
            "canGenerate": count < MAX_VIDEOS_PER_USER
        }), 200
    except Exception as e:
        logger.error(f"Error checking video limit: {e}")
        return jsonify({"error": str(e)}), 500

@app.route("/generate_video", methods=["POST"])
@token_required
def generate_video(current_user):
    try:
        # Check if the user has reached their video limit
        video_count = get_user_video_count(current_user['id'])
        if video_count >= MAX_VIDEOS_PER_USER:
            return jsonify({
                "error": f"You have reached the maximum limit of {MAX_VIDEOS_PER_USER} videos. Please delete some videos before generating new ones.",
                "videoCount": video_count,
                "limit": MAX_VIDEOS_PER_USER
            }), 403

        # Get form data
        min_time = float(request.form.get("minTime", 3))
        max_time = float(request.form.get("maxTime", 5))
        image_selection = request.form.get("imageSelection", "ascending")
        transition_type = request.form.get("transitionType", "fade")
        transition_time = float(request.form.get("transitionTime", 0.5))
        voice_volume = float(request.form.get("voiceVolume", 1.0))
        background_volume = float(request.form.get("backgroundVolume", 0.3))
        text_overlays = request.form.getlist("textOverlays")

        # Validate uploaded files
        if 'images' not in request.files or 'voice' not in request.files or 'backgroundSound' not in request.files:
            return jsonify({"error": "Missing required files"}), 400

        images = request.files.getlist('images')
        voice_file = request.files['voice']
        background_sound = request.files['backgroundSound']

        # Clear previous files
        for folder in [IMAGE_FOLDER, VOICE_FOLDER, BACKGROUND_FOLDER]:
            clear_folder(folder)

        # Save uploaded files
        image_paths = []
        for img in images:
            if img and img.filename:
                filename = secure_filename(img.filename)
                filepath = os.path.join(IMAGE_FOLDER, filename)
                img.save(filepath)
                image_paths.append(filepath)

        # Apply image selection logic
        if image_selection == "random":
            random.shuffle(image_paths)
        elif image_selection == "descending":
            image_paths.reverse()
        # "ascending" is default and requires no change to the list

        voice_path = os.path.join(VOICE_FOLDER, secure_filename(voice_file.filename))
        voice_file.save(voice_path)

        background_path = os.path.join(BACKGROUND_FOLDER, secure_filename(background_sound.filename))
        background_sound.save(background_path)

        # Process audio
        voice_audio = AudioFileClip(voice_path).volumex(voice_volume)
        voice_duration = voice_audio.duration

        background_audio = AudioFileClip(background_path).volumex(background_volume)
        if background_audio.duration < voice_duration:
            background_audio = background_audio.loop(duration=voice_duration)
        else:
            background_audio = background_audio.subclip(0, voice_duration)

        # Generate video clips
        clips = []
        total_duration = 0
        img_index = 0

        while total_duration < voice_duration and image_paths:
            duration = min(get_random_duration(min_time, max_time), 
                         voice_duration - total_duration)
            
            img_path = image_paths[img_index % len(image_paths)]
            clip = ImageClip(img_path).set_duration(duration)

            if img_index < len(text_overlays) and text_overlays[img_index]:
                text = TextClip(
                    text_overlays[img_index],
                    fontsize=50,
                    color='white',
                    size=clip.size,
                    method="caption"
                ).set_position(('center', 'bottom')).set_duration(duration)
                clip = CompositeVideoClip([clip, text])

            clips.append(clip)
            total_duration += duration
            img_index += 1

        # Apply transitions and combine clips
        final_clips = [clips[0]]
        for i in range(1, len(clips)):
            clip1, clip2 = apply_transition_effects(
                final_clips[-1], 
                clips[i], 
                transition_type, 
                transition_time
            )
            final_clips[-1] = clip1
            final_clips.append(clip2)

        # Create final video
        final_video = concatenate_videoclips(final_clips, method="compose")
        final_video = final_video.set_audio(
            CompositeAudioClip([voice_audio, background_audio])
        )

        # Save video to user-specific folder
        output_filename = generate_unique_filename()
        user_folder = get_user_output_folder(current_user['id'])
        output_path = os.path.join(user_folder, output_filename)
        
        final_video.write_videofile(
            output_path,
            codec="libx264",
            audio_codec="aac",
            fps=24,
            threads=4,
            logger=None
        )

        # Save video record in database
        save_video_record(current_user['id'], output_filename, voice_duration)

        # Clean up
        final_video.close()
        voice_audio.close()
        background_audio.close()
        for clip in clips:
            clip.close()

        # Clear input files
        for folder in [IMAGE_FOLDER, VOICE_FOLDER, BACKGROUND_FOLDER]:
            clear_folder(folder)

        # Get updated video count
        new_count = get_user_video_count(current_user['id'])

        video_url = url_for('serve_video', filename=output_filename, _external=True)
        return jsonify({
            "message": "Video generated successfully",
            "videoUrl": video_url,
            "filename": output_filename,
            "videoCount": new_count,
            "limit": MAX_VIDEOS_PER_USER
        }), 200

    except Exception as e:
        logger.error(f"Error generating video: {e}")
        return jsonify({"error": str(e)}), 500

@app.route('/')
def home():
    return jsonify({'message': 'Backend running'}), 200

@app.route('/favicon.ico')
def favicon():
    return '', 204  # No Content

@app.route('/signin', methods=['POST', 'OPTIONS'])
def signin():
    if request.method == 'OPTIONS':
        response = jsonify({})
        response.headers.add('Access-Control-Allow-Methods', 'POST')
        response.headers.add('Access-Control-Allow-Headers', 'Content-Type')
        return response

    try:
        data = request.get_json()

        if not data or not data.get('email') or not data.get('password'):
            return jsonify({
                'success': False,
                'message': 'Please provide email and password'
            }), 400

        conn = get_db_connection()
        if not conn:
            return jsonify({
                'success': False,
                'message': 'Database connection failed'
            }), 500

        cursor = conn.cursor(dictionary=True)
        cursor.execute("SELECT * FROM users WHERE email = %s", (data['email'],))
        user = cursor.fetchone()

        if not user:
            return jsonify({
                'success': False,
                'message': 'User not found. Please sign up',
                'needsSignup': True
            }), 404

        if user['password'] != data['password']:
            return jsonify({
                'success': False,
                'message': 'Incorrect email or password'
            }), 401

        # Check subscription status
        subscription_expired = False
        if user['subscription_expiry']:
            subscription_expired = datetime.strptime(str(user['subscription_expiry']), '%Y-%m-%d').date() < datetime.now().date()

        # Generate JWT token
        token = jwt.encode({
            'user_id': user['id'],
            'exp': datetime.now(timezone.utc) + timedelta(seconds=app.config['JWT_EXPIRATION'])
        }, app.config['SECRET_KEY'], algorithm="HS256")

        # Update auth_key in the database
        cursor.execute("UPDATE users SET auth_key = %s WHERE id = %s", (token, user['id']))
        conn.commit()

        cursor.close()
        conn.close()

        return jsonify({
            'success': True,
            'message': 'Sign in successful',
            'token': token,
            'user': {
                'id': user['id'],
                'email': user['email'],
                'name': user['name'],
                'subscription': user['subscription'],
                'subscription_expiry': str(user['subscription_expiry']) if user['subscription_expiry'] else None,
                'subscription_expired': subscription_expired
            }
        }), 200

    except Exception as e:
        logger.error(f"Signin error: {str(e)}")
        return jsonify({
            'success': False,
            'message': 'Internal server error'
        }), 500

@app.route('/signup', methods=['POST'])
def signup():
    try:
        data = request.get_json()
        required_fields = ['email', 'password', 'name', 'confirmPassword']

        if not all(field in data for field in required_fields):
            return jsonify({'error': 'Missing required fields'}), 400

        if data['password'] != data['confirmPassword']:
            return jsonify({'error': 'Passwords do not match'}), 400

        conn = get_db_connection()
        if not conn:
            return jsonify({'error': 'Database connection failed'}), 500

        cursor = conn.cursor(dictionary=True)
        cursor.execute("SELECT * FROM users WHERE email = %s", (data['email'],))
        existing_user = cursor.fetchone()

        if existing_user:
            return jsonify({'error': 'Email already registered'}), 409

        # Set default subscription values
        default_subscription = 'free'
        default_expiry = (datetime.now() + timedelta(days=30)).date()  # 30-day trial

        # Insert the new user with subscription details
        cursor.execute(
            """INSERT INTO users (email, password, name, subscription, subscription_expiry) 
            VALUES (%s, %s, %s, %s, %s)""",
            (data['email'], data['password'], data['name'], default_subscription, default_expiry)
        )
        conn.commit()
        new_user_id = cursor.lastrowid

        # Generate JWT token
        token = jwt.encode({
            'user_id': new_user_id,
            'exp': datetime.now(timezone.utc) + timedelta(seconds=app.config['JWT_EXPIRATION'])
        }, app.config['SECRET_KEY'], algorithm="HS256")

        # Update auth_key for the new user
        cursor.execute(
            """UPDATE users 
            SET auth_key = %s 
            WHERE id = %s""",
            (token, new_user_id)
        )
        conn.commit()

        cursor.close()
        conn.close()

        # Send welcome email to newly registered user
        try:
            # Get SMTP settings from environment variables
            smtp_host = os.getenv('SMTP_HOST')
            smtp_port = int(os.getenv('SMTP_PORT'))
            smtp_user = os.getenv('SMTP_USER')
            smtp_password = os.getenv('SMTP_PASSWORD')
            smtp_from = os.getenv('SMTP_FROM')
            
            # Create email message
            msg = EmailMessage()
            
            # HTML content for welcome email
            html_content = f"""
            <html>
                <head>
                    <style>
                        body {{ font-family: Arial, sans-serif; line-height: 1.6; color: #333; }}
                        .container {{ max-width: 600px; margin: 0 auto; padding: 20px; }}
                        .header {{ background-color: #4a86e8; color: white; padding: 10px 20px; text-align: center; }}
                        .content {{ padding: 20px; background-color: #f9f9f9; }}
                        .footer {{ text-align: center; margin-top: 20px; font-size: 12px; color: #777; }}
                    </style>
                </head>
                <body>
                    <div class="container">
                        <div class="header">
                            <h1>Welcome to Our GEN VIDEO AI</h1>
                        </div>
                        <div class="content">
                            <h2>Hello {data['name']},</h2>
                            <p>Thank you for signing up with us! We're excited to have you on board.</p>
                            <p>Your account has been successfully created. Please upgrade to Pro at just ₹10/month and enjoy unlimited video generation.</p>
                            <ul>
                            </ul>
                            <p>If you have any questions or need assistance, feel free to contact our support team.</p>
                            <p>Best regards,<br>The Team</p>
                        </div>
                        <div class="footer">
                            <p>This is an automated message. Please do not reply to this email.</p>
                        </div>
                    </div>
                </body>
            </html>
            """
            
            # Set email content with HTML
            msg.set_content("Thank you for signing up to our platform!")
            msg.add_alternative(html_content, subtype='html')
            
            msg['Subject'] = 'Welcome to Our Platform! GEN VIDEO AI'
            msg['From'] = smtp_from
            msg['To'] = data['email']

            # Send the welcome email
            with smtplib.SMTP(smtp_host, smtp_port) as smtp:
                smtp.starttls()
                smtp.login(smtp_user, smtp_password)
                smtp.send_message(msg)
                logger.info(f"Welcome email sent to {data['email']}")
                
        except Exception as e:
            # Log the error but don't stop the signup process
            logger.error(f"Failed to send welcome email: {str(e)}")
            # Continue with the signup process even if email fails

        return jsonify({
            'message': 'User created successfully',
            'token': token,
            'user': {
                'id': new_user_id,
                'email': data['email'],
                'name': data['name'],
                'subscription': default_subscription,
                'subscription_expiry': str(default_expiry),
                'subscription_expired': False
            }
        }), 201

    except Exception as e:
        logger.error(f"Signup error: {str(e)}")
        return jsonify({'error': 'Internal server error'}), 500

@app.route('/update-subscription', methods=['POST'])
def update_subscription():
    try:
        data = request.get_json()
        user_id = data.get('user_id')
        new_subscription = data.get('subscription')
        new_expiry = data.get('expiry')

        if not all([user_id, new_subscription, new_expiry]):
            return jsonify({'error': 'Missing required fields'}), 400

        conn = get_db_connection()
        if not conn:
            return jsonify({'error': 'Database connection failed'}), 500

        cursor = conn.cursor()
        cursor.execute(
            """UPDATE users 
            SET subscription = %s, subscription_expiry = %s 
            WHERE id = %s""",
            (new_subscription, new_expiry, user_id)
        )
        conn.commit()
        cursor.close()
        conn.close()

        return jsonify({
            'message': 'Subscription updated successfully',
            'subscription': new_subscription,
            'expiry': new_expiry
        }), 200

    except Exception as e:
        logger.error(f"Update subscription error: {str(e)}")
        return jsonify({'error': 'Internal server error'}), 500

@app.route('/forgot-password', methods=['POST'])
def forgot_password():
    data = request.get_json()
    email = data.get('email')

    if not email:
        return jsonify({'error': 'Email is required'}), 400

    conn = get_db_connection()
    cursor = conn.cursor(dictionary=True)
    cursor.execute("SELECT * FROM users WHERE email = %s", (email,))
    user = cursor.fetchone()

    if not user:
        cursor.close()
        conn.close()
        return jsonify({'message': 'If the email exists, a reset link will be sent'}), 200  # avoid revealing existence

    # Generate token
    token = jwt.encode(
        {'user_id': user['id'], 'exp': datetime.now(timezone.utc) + timedelta(hours=RESET_TOKEN_EXPIRY_HOURS)},
        app.config['SECRET_KEY'],
        algorithm='HS256'
    )

    # Store token and expiry
    cursor.execute("UPDATE users SET reset_token = %s, reset_token_expiry = %s WHERE id = %s",
                   (token, datetime.now() + timedelta(hours=RESET_TOKEN_EXPIRY_HOURS), user['id']))
    conn.commit()
    cursor.close()
    conn.close()

    # Get SMTP settings from environment variables
    smtp_host = os.getenv('SMTP_HOST')
    smtp_port = int(os.getenv('SMTP_PORT'))
    smtp_user = os.getenv('SMTP_USER')
    smtp_password = os.getenv('SMTP_PASSWORD')
    smtp_from = os.getenv('SMTP_FROM')
    
    # Get frontend URL from environment
    #frontend_url = os.getenv('NEXT_PUBLIC_API_URL', 'http://localhost:3000')
    frontend_url = os.getenv('NEXT_PUBLIC_API_URL')
    reset_url = f"{frontend_url}/reset-password?token={token}"

    # Create email message
    msg = EmailMessage()
    msg.set_content(f"Click the link to reset your password: {reset_url}")
    msg['Subject'] = 'Password Reset Request'
    msg['From'] = smtp_from
    msg['To'] = email

    try:
        with smtplib.SMTP(smtp_host, smtp_port) as smtp:
            smtp.starttls()
            smtp.login(smtp_user, smtp_password)
            smtp.send_message(msg)
            logger.info(f"Password reset email sent to {email}")
    except Exception as e:
        logger.error(f"Failed to send email: {str(e)}")
        return jsonify({'error': f"Failed to send email: {str(e)}"}), 500

    return jsonify({'message': 'Password reset link sent'}), 200

@app.route('/reset-password', methods=['POST'])
def reset_password():
    data = request.get_json()
    token = data.get('token')
    new_password = data.get('new_password')

    if not token or not new_password:
        return jsonify({'error': 'Token and new password are required'}), 400

    try:
        payload = jwt.decode(token, app.config['SECRET_KEY'], algorithms=["HS256"])
        user_id = payload['user_id']

        conn = get_db_connection()
        cursor = conn.cursor(dictionary=True)

        cursor.execute("SELECT * FROM users WHERE id = %s AND reset_token = %s", (user_id, token))
        user = cursor.fetchone()

        if not user:
            cursor.close()
            conn.close()
            return jsonify({'error': 'Invalid token'}), 400

        # Check if token is expired
        if user.get('reset_token_expiry') and user['reset_token_expiry'] < datetime.now():
            cursor.close()
            conn.close()
            return jsonify({'error': 'Token expired'}), 400

        # Store plain password since your login function compares plain passwords
        cursor.execute("UPDATE users SET password = %s, reset_token = NULL, reset_token_expiry = NULL WHERE id = %s",
                      (new_password, user_id))
        conn.commit()
        cursor.close()
        conn.close()

        return jsonify({'message': 'Password has been reset successfully'}), 200

    except jwt.ExpiredSignatureError:
        return jsonify({'error': 'Token expired'}), 400
    except jwt.InvalidTokenError:
        return jsonify({'error': 'Invalid token'}), 400
    except Exception as e:
        logger.error(f"Reset password error: {str(e)}")
        return jsonify({'error': f'Unexpected error: {str(e)}'}), 500

@app.route('/create_payment', methods=['POST'])
@token_required
def create_payment(current_user):
    try:
        data = request.json
        amount = data.get("amount")
        subscription_type = data.get("subscription_type")
        duration_days = data.get("duration_days", 30)
        phone_number = data.get("phone_number")  # Get phone number from request
        
        if not all([amount, subscription_type, phone_number]):
            return jsonify({"error": "Missing required fields (amount, subscription_type, phone_number)"}), 400

        # Generate order ID using timestamp
        timestamp = int(datetime.now().timestamp())
        unique_id = str(uuid.uuid4())[:8]
        order_id = f"order_{timestamp}_{unique_id}"
        
        headers = {
            "Content-Type": "application/json",
            "x-client-id": CASHFREE_APP_ID,
            "x-client-secret": CASHFREE_SECRET_KEY,
            "x-api-version": "2022-09-01"
        }

        order_payload = {
            "order_id": order_id,
            "order_amount": amount,
            "order_currency": "INR",
            "order_note": f"Payment for {subscription_type} subscription",
            "customer_details": {
                "customer_id": str(current_user['id']),
                "customer_name": current_user['name'],
                "customer_email": current_user['email'],
                "customer_phone": phone_number  # Use phone number from request
            },
            "order_meta": {
                "return_url": f"{frontend_url}/payment_success?order_id={order_id}",
                "notify_url": f"{frontend_url}/payment_webhook"
            }
        }

        logger.info(f"Creating order with payload: {json.dumps(order_payload, indent=2)}")
        
        order_response = requests.post(
            f"{CASHFREE_BASE_URL}/orders",
            json=order_payload,
            headers=headers
        )
        
        if order_response.status_code == 200:
            order_data = order_response.json()
            cf_order_id = order_data.get('cf_order_id')
            
            if cf_order_id:
                # Save initial payment record (without phone number)
                conn = get_db_connection()
                cursor = conn.cursor()
                cursor.execute("""
                    INSERT INTO payment_orders (
                        order_id, user_id, amount, subscription_type, 
                        duration_days, status, created_at
                    ) VALUES (%s, %s, %s, %s, %s, %s, %s)
                """, (
                    order_id,
                    current_user['id'],
                    amount,
                    subscription_type,
                    duration_days,
                    'INITIATED',
                    datetime.now()
                ))
                conn.commit()
                cursor.close()
                conn.close()
                
                # Generate payment link using cf_order_id
                payment_link = f"https://payments.cashfree.com/order/#/{cf_order_id}" #for deployment
                
                # Print order details to terminal
                print("\nOrder created successfully!")
                print(f"Order ID: {order_id}")
                print(f"CF Order ID: {cf_order_id}")
                print(f"Amount: {amount} INR")
                print(f"Status: {order_data.get('order_status')}")
                print(f"Payment Link: {payment_link}")
                print(f"Expiry: {order_data.get('order_expiry_time')}")
                
                # Print full response for debugging
                print("\nFull Response:")
                print(json.dumps(order_data, indent=2))
                
                return jsonify({
                    "status": "success",
                    "order_id": order_id,
                    "cf_order_id": cf_order_id,
                    "payment_link": payment_link,
                    "amount": amount,
                    "currency": "INR",
                    "order_status": order_data.get('order_status'),
                    "order_expiry": order_data.get('order_expiry_time'),
                    "order_details": order_data
                }), 200
            else:
                print("\nError: No CF order ID in response")
                print("Response details:", json.dumps(order_data, indent=2))
                return jsonify({
                    "error": "No CF order ID in response",
                    "details": order_data
                }), 400
        else:
            print("\nError: Failed to create order")
            print("Response:", order_response.text)
            return jsonify({
                "error": "Failed to create order",
                "details": order_response.json()
            }), order_response.status_code

    except Exception as e:
        print(f"\nError creating payment: {str(e)}")
        logger.error(f"Payment creation error: {str(e)}")
        return jsonify({"error": str(e)}), 500

@app.route('/payment_success')
@token_required
def payment_success(current_user):
    try:
        order_id = request.args.get('order_id')
        
        headers = {
            "x-client-id": CASHFREE_APP_ID,
            "x-client-secret": CASHFREE_SECRET_KEY,
            "x-api-version": "2022-09-01"
        }
        
        response = requests.get(
            f"{CASHFREE_BASE_URL}/orders/{order_id}",
            headers=headers
        )
        
        if response.status_code == 200:
            order_data = response.json()
            is_paid = order_data.get('order_status') == "PAID"
            
            if is_paid:
                # Get order details from database
                conn = get_db_connection()
                cursor = conn.cursor(dictionary=True)
                cursor.execute("""
                    SELECT * FROM payment_orders 
                    WHERE order_id = %s AND user_id = %s
                """, (order_id, current_user['id']))
                order_details = cursor.fetchone()
                
                if order_details:
                    # Update subscription
                    success = update_subscription_status(
                        current_user['id'],
                        order_details['subscription_type'],
                        order_details['duration_days']
                    )
                    
                    if success:
                        # Save payment record
                        save_payment_record(order_id, current_user['id'], 
                                         order_details['amount'], order_data)
                        
                        # Update order status
                        cursor.execute("""
                            UPDATE payment_orders 
                            SET status = %s, updated_at = %s 
                            WHERE order_id = %s
                        """, ('COMPLETED', datetime.now(), order_id))
                        conn.commit()
                
                cursor.close()
                conn.close()
            
            return jsonify({
                "status": "success",
                "order_id": order_id,
                "order_status": order_data.get('order_status'),
                "payment_details": order_data
            })
        else:
            return jsonify({
                "status": "error",
                "message": "Failed to verify payment"
            }), 400
            
    except Exception as e:
        logger.error(f"Payment success error: {str(e)}")
        return jsonify({"error": str(e)}), 500
    
# Updated check_subscription endpoint
@app.route('/check_subscription', methods=['GET'])
@token_required  # Allow checking subscription even if expired
def check_subscription(current_user):
    try:
        conn = get_db_connection()
        cursor = conn.cursor(dictionary=True)
        
        # Calculate if subscription is expired
        subscription_expired = False
        is_active = False
        
        if current_user['subscription_expiry']:
            expiry_date = datetime.strptime(str(current_user['subscription_expiry']), '%Y-%m-%d').date()
            subscription_expired = expiry_date < datetime.now().date()
            is_active = not subscription_expired and current_user['subscription'] != 'free'
        
        # Get latest payment status if any
        cursor.execute("""
            SELECT order_id, status, created_at 
            FROM payment_orders 
            WHERE user_id = %s 
            ORDER BY created_at DESC 
            LIMIT 1
        """, (current_user['id'],))
        
        latest_payment = cursor.fetchone()
        
        cursor.close()
        conn.close()
        
        return jsonify({
            "isPro": is_active,
            "subscription": {
                "type": current_user["subscription"],
                "expiryDate": str(current_user["subscription_expiry"]) if current_user["subscription_expiry"] else None,
                "isExpired": subscription_expired
            },
            "latestPayment": {
                "orderId": latest_payment["order_id"] if latest_payment else None,
                "status": latest_payment["status"] if latest_payment else None,
                "date": latest_payment["created_at"].isoformat() if latest_payment else None
            } if latest_payment else None
        }), 200
        
    except Exception as e:
        app.logger.error(f"Error checking subscription: {str(e)}")
        return jsonify({"error": str(e)}), 500

@app.route('/session', methods=['GET', 'POST'])
def get_session():
    try:
        # For POST request with email in body
        if request.method == 'POST':
            data = request.get_json()
            email = data.get('email')
            if not email:
                return jsonify({'user': None, 'error': 'Email is required'}), 400
        # For GET request with email in query params or headers
        else:
            email = request.args.get('email') or request.headers.get('X-User-Email')
            if not email:
                return jsonify({'user': None, 'error': 'Email is required in query params or X-User-Email header'}), 400
        
        # Get user from database by email
        conn = get_db_connection()
        cursor = conn.cursor(dictionary=True)
        cursor.execute("SELECT * FROM users WHERE email = %s", (email,))
        user = cursor.fetchone()
        
        if not user:
            cursor.close()
            conn.close()
            return jsonify({'user': None, 'error': 'User not found'}), 404
        
        # Check subscription status
        subscription_expired = False
        if user['subscription_expiry']:
            subscription_expired = datetime.strptime(str(user['subscription_expiry']), '%Y-%m-%d').date() < datetime.now().date()
        
        # Check if token exists and is valid
        current_token = user.get('auth_key')
        token_is_valid = False
        
        # If user doesn't have an auth_key (logged out), return user: null but with 200 OK
        if not current_token:
            cursor.close()
            conn.close()
            return jsonify({'user': None, 'logged_in': False}), 200
        
        if current_token:
            try:
                # Try to decode the token to check if it's valid
                decoded_token = jwt.decode(current_token, app.config['SECRET_KEY'], algorithms=["HS256"])
                # Check if token is expired
                exp_timestamp = decoded_token.get('exp')
                if exp_timestamp:
                    # Convert to datetime
                    exp_datetime = datetime.fromtimestamp(exp_timestamp, tz=timezone.utc)
                    # Check if token is still valid
                    if exp_datetime > datetime.now(timezone.utc):
                        token_is_valid = True
            except jwt.ExpiredSignatureError:
                # Token has expired
                pass
            except jwt.InvalidTokenError:
                # Token is invalid
                pass
        
        # Generate a new token only if the current one is invalid or expired
        if not token_is_valid:
            # If the token is invalid but exists, refresh it
            if current_token:
                # Generate new JWT token
                new_token = jwt.encode({
                    'user_id': user['id'],
                    'exp': datetime.now(timezone.utc) + timedelta(seconds=app.config['JWT_EXPIRATION'])
                }, app.config['SECRET_KEY'], algorithm="HS256")
                
                # Update auth_key in the database
                cursor.execute("UPDATE users SET auth_key = %s WHERE id = %s", (new_token, user['id']))
                conn.commit()
                
                # Use the new token
                current_token = new_token
                logger.info(f"Generated new token for user {user['id']} as previous token was expired or invalid")
            else:
                # User has no token (logged out) - return success with null user
                cursor.close()
                conn.close()
                return jsonify({'user': None, 'logged_in': False}), 200
        
        cursor.close()
        conn.close()
        
        # Return user data (excluding sensitive information) along with the token
        return jsonify({
            'user': {
                'id': user['id'],
                'email': user['email'],
                'name': user['name'],
                'subscription': user['subscription'],
                'subscription_expiry': str(user['subscription_expiry']) if user['subscription_expiry'] else None,
                'subscription_expired': subscription_expired
            },
            'token': current_token,
            'logged_in': True
        }), 200
            
    except Exception as e:
        app.logger.error(f"Session check error: {str(e)}")
        return jsonify({'user': None, 'error': f'Internal server error: {str(e)}'}), 500
    
@app.route('/payment_webhook', methods=['POST'])
def payment_webhook():
    conn = None
    cursor = None
    try:
        webhook_data = request.json
        app.logger.info(f"Received webhook data: {json.dumps(webhook_data, indent=2)}")
        
        if not webhook_data or 'data' not in webhook_data:
            app.logger.error("Invalid webhook data received")
            return jsonify({"error": "Invalid webhook data"}), 400

        # Extract order data
        order_data = webhook_data.get('data', {}).get('order', {})
        order_id = order_data.get('order_id')

        if not order_id:
            app.logger.error("Missing order_id in webhook data")
            return jsonify({"error": "Missing order_id"}), 400

        # Get payment details from Cashfree API
        headers = {
            "x-client-id": CASHFREE_APP_ID,
            "x-client-secret": CASHFREE_SECRET_KEY,
            "x-api-version": "2022-09-01"
        }
        
        response = requests.get(
            f"{CASHFREE_BASE_URL}/orders/{order_id}",
            headers=headers
        )
        
        if response.status_code != 200:
            app.logger.error(f"Failed to fetch order details from Cashfree: {response.text}")
            return jsonify({"error": "Failed to verify order status"}), 400

        payment_details = response.json()
        is_paid = payment_details.get('order_status') == "PAID"

        app.logger.info(f"Order {order_id} payment status: {payment_details.get('order_status')}")

        if is_paid:
            # Create a new connection for this request
            conn = mysql.connector.connect(**DATABASE_CONFIG)
            cursor = conn.cursor(dictionary=True)
            
            # Check if payment was already processed
            cursor.execute("""
                SELECT status FROM payment_orders 
                WHERE order_id = %s FOR UPDATE
            """, (order_id,))
            existing_order = cursor.fetchone()
            
            if existing_order and existing_order['status'] == 'COMPLETED':
                app.logger.info(f"Payment for order {order_id} was already processed")
                return jsonify({
                    "status": "success",
                    "message": "Payment already processed"
                }), 200

            # Get order details
            cursor.execute("""
                SELECT * FROM payment_orders 
                WHERE order_id = %s
            """, (order_id,))
            order_details = cursor.fetchone()
            
            if not order_details:
                app.logger.error(f"Order details not found for order_id: {order_id}")
                return jsonify({"error": "Order not found"}), 404

            try:
                # Update subscription
                cursor.execute("""
                    UPDATE users 
                    SET subscription = %s,
                        subscription_expiry = %s 
                    WHERE id = %s
                """, (
                    order_details['subscription_type'],
                    (datetime.now() + timedelta(days=order_details['duration_days'])).date(),
                    order_details['user_id']
                ))

                # Save payment record
                cursor.execute("""
                    INSERT INTO payments (
                        order_id, user_id, amount, payment_status,
                        payment_method, transaction_id, payment_date
                    ) VALUES (%s, %s, %s, %s, %s, %s, %s)
                """, (
                    order_id,
                    order_details['user_id'],
                    order_details['amount'],
                    payment_details.get('order_status'),
                    payment_details.get('payment_method', 'unknown'),
                    payment_details.get('cf_payment_id', ''),
                    datetime.now()
                ))

                # Update order status
                cursor.execute("""
                    UPDATE payment_orders 
                    SET status = %s,
                        updated_at = %s,
                        payment_response = %s
                    WHERE order_id = %s
                """, ('COMPLETED', datetime.now(), json.dumps(payment_details), order_id))
                
                # Commit all changes
                conn.commit()
                app.logger.info(f"Successfully processed payment for order {order_id}")
                
                return jsonify({
                    "status": "success",
                    "message": f"Payment successfully processed for order {order_id}",
                    "order_status": payment_details.get('order_status'),
                    "payment_details": payment_details
                }), 200

            except Exception as e:
                if conn:
                    conn.rollback()
                app.logger.error(f"Error in database operations: {str(e)}")
                return jsonify({"error": f"Database operation error: {str(e)}"}), 500

        else:
            app.logger.info(f"Payment not successful for order {order_id}. Status: {payment_details.get('order_status')}")
            return jsonify({
                "status": "pending",
                "message": f"Payment not successful for order {order_id}",
                "order_status": payment_details.get('order_status')
            }), 200

    except Exception as e:
        if conn and conn.is_connected():
            conn.rollback()
        app.logger.error(f"Webhook processing error: {str(e)}")
        return jsonify({"error": str(e)}), 500
        
    finally:
        if cursor:
            cursor.close()
        if conn and conn.is_connected():
            conn.close()

# Fixed logout endpoint - should work even with expired subscription
@app.route('/logout', methods=['POST'])
@token_required  # Use token_required instead of subscription_required
def logout(current_user):
    try:
        conn = get_db_connection()
        if not conn:
            return jsonify({
                'success': False,
                'message': 'Database connection failed'
            }), 500

        cursor = conn.cursor()
        
        # Set auth_key to NULL to invalidate the token
        cursor.execute("UPDATE users SET auth_key = NULL WHERE id = %s", (current_user['id'],))
        conn.commit()
        
        cursor.close()
        conn.close()

        response = jsonify({
            'success': True,
            'message': 'Logged out successfully'
        })
        
        return response, 200

    except Exception as e:
        logger.error(f"Logout error: {str(e)}")
        return jsonify({
            'success': False,
            'message': 'Internal server error'
        }), 500

# CORS configuration
@app.after_request
def after_request(response):
    response.headers.add('Access-Control-Allow-Origin', '*')
    response.headers.add('Access-Control-Allow-Headers', 'Content-Type,Authorization')
    response.headers.add('Access-Control-Allow-Methods', 'GET,POST,DELETE,OPTIONS')
    return response

if __name__ == '__main__':
    #import os
    # In production, debug should be False
    debug_mode = os.getenv('FLASK_DEBUG', 'False').lower() == 'true'
    port = int(os.environ.get('PORT', 5000))  # Default to 5000 if not set
    app.run(host='0.0.0.0', port=port, debug=debug_mode)
