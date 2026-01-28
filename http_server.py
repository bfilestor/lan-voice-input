"""Flask app serving the web UI and runtime config."""
from flask import Flask, jsonify, send_file

from paths import resource_path


def create_app(get_url_state):
    """
    get_url_state should return a dict:
    {"http_port": int, "ws_port": int, "url": str}
    """
    app = Flask(__name__)

    @app.route("/")
    def index():
        return send_file(resource_path("index.html"))

    @app.route("/config")
    def config():
        state = get_url_state()
        return jsonify(
            {
                "ws_port": state.get("ws_port"),
                "http_port": state.get("http_port"),
                "url": state.get("url"),
            }
        )

    return app


def run_http(get_url_state):
    state = get_url_state()
    app = create_app(get_url_state)
    app.run(host="0.0.0.0", port=state.get("http_port"), debug=False, use_reloader=False)
