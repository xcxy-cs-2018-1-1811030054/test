name: Build Windows EXE

on:
  workflow_dispatch:
  push:
    tags:
      - "v*"

jobs:
  build-windows:
    runs-on: windows-latest

    steps:
      - name: 检出代码
        uses: actions/checkout@v4

      - name: 安装 Python 3.8
        uses: actions/setup-python@v5
        with:
          python-version: "3.8"

      - name: 显示环境信息
        run: |
          python --version
          python -c "import sys; print('Executable:', sys.executable)"
        shell: cmd

      - name: 安装 PyInstaller
        run: |
          python -m pip install --upgrade pip
          python -m pip install "pyinstaller==5.13.2"
        shell: cmd

      - name: 打包成单文件 EXE
        run: |
          python -m PyInstaller --noconfirm --clean --onefile --windowed --name VideoDedup video_dedup_gui.py
        shell: cmd

      - name: 校验产物确实生成了
        run: |
          dir dist
          if not exist "dist\VideoDedup.exe" (
            echo [ERROR] exe was not generated!
            exit /b 1
          )
          echo [OK] exe generated successfully
        shell: cmd

      - name: 上传 EXE
        uses: actions/upload-artifact@v4
        with:
          name: VideoDedup-windows
          path: dist/VideoDedup.exe
