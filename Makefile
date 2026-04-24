
EXECUTABLE = basic-plus
GITPATH = ~/git/basic-plus

include common.mk

install: $(EXECUTABLE)
	sudo install -v $(EXECUTABLE) /usr/local/bin

git:
	rsync -a $(EXECUTABLE) $(DOCS) $(GO_FILES) Makefile \
		go.mod go.sum $(GITPATH)

lint:
	golangci-lint run
