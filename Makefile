.PHONY: extension

# Run `make extension` to rebuild the extension in development.
# After that, manually close and open vscode (unfortunately that's hard to do programmatically).
extension:
	cd extension && \
	vsce package --out paperproof.vsix && \
	code --uninstall-extension paperproof.paperproof || true && \
	code --install-extension paperproof.vsix
