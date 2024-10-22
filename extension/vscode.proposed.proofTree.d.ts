/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/

declare module "vscode" {
  /** Lean proof tree */
  export type ProofTree = any;

  /** Proof tree provider */
  export interface ProofTreeProvider {
    /** Provide the proof tree for the given document */
    provideProofTree(
      document: TextDocument,
      position: Position,
      token: CancellationToken
    ): ProviderResult<ProofTree>;
  }

  export namespace languages {
    /** */
    export function registerProofTreeProvider(
      selector: DocumentSelector,
      provider: ProofTreeProvider
    ): Disposable;
  }
}
