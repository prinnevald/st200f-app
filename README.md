# st200f-app

A quick app that I vibecoded for the Samsung ST200F camera that I have, since Samsung MobileLink app is stuck in 2015 and does not work on modern Android versions.

Yes, this is not an Android app, but a terminal-based prototype. Just run by doing:

python st200f-app.py
(or python3, depending on what you have)

I first like to start the app, then start the MobileLink on the camera, and then do:

1. Connect to camera Wi-Fi
2. Laptop Wi-Fi IP: 192.168.11.12 (should be default)
3. Click Listen UDP 1901
4. Wait until it detects the camera (The line near the Browse Root now has a directory)
5. It should create a Samsung Camera MediaServer device
6. Click Browse root
7. Double-click 100PHOTO
8. Voila, you have your files

There is also an implementation by IstvanSafar: SamsungCameraDownloader, but that one seems to be running on Win and not linux (so I rolled with what I have)

My next steps are to turn all this into an Android app.
