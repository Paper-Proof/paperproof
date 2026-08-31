import React from "react";

interface Props {
  children: React.ReactNode;
  onError?: () => void;
}

class ProofTreeErrorBoundary extends React.Component<Props, { hasError: boolean; message: string }> {
  constructor(props: Props) {
    super(props);
    this.state = { hasError: false, message: '' };
  }
  static getDerivedStateFromError(error: Error) {
    return { hasError: true, message: error.message };
  }
  componentDidCatch() {
    this.props.onError?.();
  }
  render() {
    if (this.state.hasError) {
      return (
        <div className="natural-render-error">
          Renderer error: {this.state.message}
        </div>
      );
    }
    return this.props.children;
  }
}

export default ProofTreeErrorBoundary;
