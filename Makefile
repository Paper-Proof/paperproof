# Run `make extension` to rebuild the extension in development.
# After that, manually close and open vscode (unfortunately that's hard to do programmatically).
extension:
	cd extension && \
	vsce package --out paperproof.vsix && \
	code --uninstall-extension paperproof.paperproof || true && \
	code --install-extension paperproof.vsix

xyz.publish:
	paperproof.xyz/deployment/push.sh
xyz.local:
	cd paperproof.xyz && node esbuild.js --watch & cd paperproof.xyz && node server.js

test:
	node tests/run.mjs

embed.publish:
	cd embed && \
	npm whoami && \
	{ ! npm view paperproof@$$(node -p 'require("./package.json").version') version >/dev/null 2>&1 || npm version patch --no-git-tag-version; } && \
	npm run build && \
	npm publish
