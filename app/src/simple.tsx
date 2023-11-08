import React from "react";

import { TransformWrapper, TransformComponent } from "react-zoom-pan-pinch";

// args to the TransofrmWrapper
// import css
export const Simple = () => 
  <TransformWrapper>{({ zoomToElement, resetTransform }) => (
    <>
      <div>
        <button
          type="button"
          onClick={() => resetTransform()}
        >
          Reset
        </button>
      </div>
      <TransformComponent
        wrapperStyle={{
          // maxWidth: "100%",
          width: "100%",
          // maxHeight: "calc(100vh - 50px)",
        }}
      >
        <div
          style={{
            background: "white",
            color: "white",
            
            
            width: "100%",
          }}
        >
          <div
            onClick={(event) => {
              console.log("clicked on red rectangle");
              zoomToElement("element1")
            }}
            id="element1"
            style={{ background: "red", opacity: 0.6, width: "200px", height: "200px" }}
          >
            Zoom element 1

            <div
              onClick={(event) => {
                event.stopPropagation();
                console.log("clicked on blue rectangle");
                zoomToElement("element2")
              }}
              id="element2"
              style={{ background: "blue", opacity: 0.6, width: "100px", height: "100px" }}
            >Zoom element 2</div>
          </div>


          <div
            onClick={(event) => {
              event.stopPropagation();
              console.log("clicked on pink rectangle");
              zoomToElement("elementHi")
            }}
            id="elementHi"
            style={{ background: "pink", opacity: 1, width: "200px", height: "200px" }}
          >
            Zoom element hi

            <div
              onClick={(event) => {
                event.stopPropagation();
                console.log("clicked on brown rectangle");
                zoomToElement("elementHello")
              }}
              id="elementHello"
              style={{ background: "brown", opacity: 1, width: "100px", height: "100px" }}
            >Zoom element hello</div>
          </div>
        </div>
      </TransformComponent>
    </>
  )}
  </TransformWrapper>
