async function copyTextToClipboard(textToCopy: string) {
  try {
    await navigator.clipboard.writeText(textToCopy);
    console.log(`copied to clipboard: ${textToCopy}`)
  } catch (error) {
    console.log('failed to copy to clipboard. error=' + error);
  }
}

export default copyTextToClipboard;
