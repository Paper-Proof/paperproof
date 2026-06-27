# Run `make extension` to rebuild the extension in development.
# After that, manually close and open vscode (unfortunately that's hard to do programmatically).
extension:
	cd extension && \
	vsce package --out paperproof.vsix && \
	code --uninstall-extension paperproof.paperproof || true && \
	code --install-extension paperproof.vsix

# We build app/standalone-rendered.html locally, and deploy everything to paperproof.xyz
xyz.production:
	cd paperproof.xyz && node esbuild.js
	cd paperproof.xyz/deployment && ./deploy.sh 128.199.52.81
xyz.local:
	cd paperproof.xyz && node esbuild.js --watch & cd paperproof.xyz && node server.js
