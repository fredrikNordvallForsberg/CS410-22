# Installing Agda on Windows 10

This short guide will help you get Agda 2.6.2.2 running on a Windows 10 machine.

1\. Install the Chocolatey package manager for Windows by following the instructions on the [Chocolatey installation page](https://chocolatey.org/install). Note that you will need an administrator PowerShell prompt.

2\. Install the [GHC Haskell compiler](https://community.chocolatey.org/packages/ghc) by running `choco install ghc` in a powershell.

3\. Run
```
cabal update
cabal install alex happy Agda
```
This will compile Agda on your machine. The process might take very long time (> 30 minutes) and is quite memory intensive (make sure you have at least 4GB free).

4\. Install emacs. You can get a Windows installer from [here](https://ftp.gnu.org/gnu/emacs/windows/emacs-27/).

5\. Create `%appdata%\.emacs` (note: no additional file extension!) and paste in the following:
```
(load-file (let ((coding-system-for-read 'utf-8))
                (shell-command-to-string "agda-mode locate")))
```
(`%appdata%` usually expands to `C:\Users\<your username>\AppData\Roaming`).

6\. Get the [agda standard library](https://github.com/agda/agda-stdlib/releases/tag/v1.7.1). Unzip it to a destination of your choice, call that parent directory `$DIR`.

7\. Create `%appdata%\agda\libraries` (note: no file extension!) and add the following line to it, replacing `$DIR` with the concrete path:
```
$DIR\agda-stdlib-1.7.1\standard-library.agda-lib
```

8\. (OPTIONAL) Create `%appdata%\agda\defaults` (again no file extension!) and add the following line to it:
```
standard-library
```
This means that all your files will know about the standard library by default. (The coursework, however, explicitly depends on the standard library, so it doesn't rely on this step.)

9\. Now you are ready to start working on your first coursework :slightly_smiling_face:. Good luck!
