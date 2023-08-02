const deleteLocalStorageItemsWithPrefix = (prefix: string): void => {
  const keysToRemove = Object.keys(localStorage).filter(key => key.startsWith(prefix));
  keysToRemove.forEach(key => localStorage.removeItem(key));
};

// Example of typical LocalStorage entry tldraw creates:
// `{ TLDRAW_USER_DATA_v3: '{"version":2,"user":{"id":"epDk1 ...`
const clearTldrawCache = () => {
  deleteLocalStorageItemsWithPrefix("TLDRAW");
}

export default clearTldrawCache;
