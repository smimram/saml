all:

RCP=rsync -rLtCPz --exclude="*.swp" --exclude="*~" --delete --stats
RHOST=$(USER)@web.sourceforge.net:/home/project-web/samlsound/htdocs
upload:
	$(RCP) . $(RHOST)