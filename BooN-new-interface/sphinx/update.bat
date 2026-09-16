rem Supprimer le repertoire docs existant (s'il existe)
rmdir ..\docs /s /q

rem Creer le repertoire docs a nouveau.
mkdir ..\docs

rem Executer make clean pour nettoyer les fichiers existants
CALL make clean

rem Executer make html pour generer la documentation HTML
CALL make html

rem Copier tous les fichiers HTML vers ../docs
xcopy /s /e /i _build\html ..\docs


