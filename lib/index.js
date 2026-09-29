/* global document window console requestAnimationFrame IntersectionObserver */

import emptyStack from '@iter-tools/imm-stack';
import classNames from 'classnames';
import { streamParse } from 'bablr';

import { CloseNodeTag, LiteralTag, OpenNodeTag, ReferenceTag } from '@bablr/agast-helpers/symbols';
import { printIdentifier, printSelfClosingNodeTag } from '@bablr/agast-helpers/print';
import { buildOpenNodeTag } from '@bablr/agast-helpers/builders';
import { parseNodeFlags, parseTag } from '@bablr/agast-helpers/parsers';
import * as BMap from '@bablr/agast-helpers/b-map';
import { hoist } from '@bablr/agast-helpers/stream';
import {
  getStreamIterator,
  StreamIterable,
  wait,
  continue_,
  evaluateReturn,
} from '@bablr/agast-helpers/iterable';
import { deepFreezeRecord, freezeRecord } from '@bablr/agast-helpers/object';
import { m } from '@bablr/helpers/grammar';

let anchorStyle =
  'display: inline-block; position: relative; vertical-align: top; pointer-events: none;';

function* siblingsFor(range) {
  let { 0: left, 1: right } = range;
  let el = left || right;

  if (!el) return;

  let backwards = left.compareDocumentPosition(right) === 2;

  do {
    yield el;
    let nextSibling = backwards ? el.previousElementSibling : el.nextElementSibling;
    if (!right || el === right || !nextSibling) break;
    el = nextSibling;
  } while (true);
}

const getCommonParentSiblings = (a, b) => {
  if (!a && !b) return [];
  if (!a) return [b, b];
  if (!b || a === b) return [a, a];

  let anode = a;
  let bnode = b;
  let rootNode = anode;
  do {
    let position = rootNode.compareDocumentPosition(b);
    if (!position || position & 0x10) {
      break;
    }
    anode = rootNode;
  } while ((rootNode = rootNode.parentNode));

  rootNode = bnode;
  do {
    let position = rootNode.compareDocumentPosition(a);
    if (!position || position & 0x10) {
      break;
    }
    bnode = rootNode;
  } while ((rootNode = rootNode.parentNode));

  return [anode, bnode];
};

const countIndents = (root) => {
  let el = root;
  let indents = 0;
  while (el) {
    if (el.classList.contains('trivia')) {
      if (el?.getAttribute('name') !== 'LeftOffset') {
        return Infinity;
      }

      let leftOffset = el;

      el = leftOffset.firstElementChild;

      while (el && el.getAttribute('name') === 'Indent') {
        indents++;
        el = el.nextElementSibling;
      }
      return indents;
    } else {
      el =
        el.previousElementSibling ||
        (el.parentElement.tagName === 'NODE' ? el.parentElement : null);
    }
  }

  return Infinity;
};

let callbacks = {};

const addDocumentEventListener = (type, cb) => {
  if (!Object.hasOwn(callbacks, type)) {
    callbacks[type] = {
      listener: (e) => {
        for (let cb of callbacks[type].callbacks) {
          cb(e);
        }
      },
      callbacks: new Set(),
    };
    document.addEventListener(type, callbacks[type].listener);
  }
  callbacks[type].callbacks.add(cb);
};

export const removeDocumentListeners = () => {
  for (let { 0: key, 1: value } of Object.entries(callbacks)) {
    document.removeEventListener(key, value.listener);
  }
};

function* __chunkify(chunkSize, str) {
  let i = -1;
  for (const chr of str) {
    if (++i === chunkSize) {
      yield wait(new Promise((resolve) => requestAnimationFrame(resolve)));
      i = -1;
    }
    yield chr;
  }
}

const chunkify = (chunkSize, str) => {
  return new StreamIterable(__chunkify(chunkSize, str));
};

function* __highlightCode(el, language, matcher, options = freezeRecord({})) {
  if (el.hasAttribute('highlighted')) return;
  el.setAttribute('highlighted', '');

  let { chunkSize, bablr: bablrOptions = {} } = options;
  // TODO instead of el.innerText make a stream source from the DOM?
  let input = chunkSize ? chunkify(chunkSize, el.innerText) : el.innerText;
  let tags = getStreamIterator(
    hoist(
      streamParse(
        language,
        matcher,
        input,
        null,
        deepFreezeRecord({
          ...bablrOptions,
          holdShiftedNodes: true,
        }),
      ),
    ),
  );

  let open;
  let referenceTag = null;
  let range = document.createRange();
  range.selectNodeContents(el.lastChild);
  let stack = emptyStack;

  let bindingTag;

  let step = tags.next();

  while (true) {
    while (step === null || step instanceof Promise) {
      if (step === null) yield continue_(), (step = tags.next());
      if (step instanceof Promise) step = yield wait(step);
    }

    if (step.done) break;

    let tag = parseTag(step.value);

    if (tag.type === OpenNodeTag) {
      range = range.cloneRange();
      range.setStart(el.lastChild, 0);
      range.setEnd(el.lastChild, 0);

      open = tag;

      if (tag.value.literalValue) {
        range.setEnd(range.startContainer, range.endOffset + tag.value.literalValue.value.length);
      }

      stack = stack.push({
        open,
        range,
        referenceTag,
      });
    }

    if (tag.type === ReferenceTag) {
      referenceTag = tag;
    }

    if (tag.type === LiteralTag) {
      let { value } = tag;
      range.setEnd(range.endContainer, range.endOffset + value.length);
    }

    if (tag.type === CloseNodeTag || (tag.type === OpenNodeTag && tag.value.selfClosing)) {
      if (stack.size > 1) {
        let doneRange = range;

        let node = document.createElement('node');
        let names = classNames({
          escape: referenceTag?.value.type === '@',
          token: open.value.flags.token,
          trivia: referenceTag?.value.type === '#',
          intrinsic: referenceTag?.value.flags.intrinsic || false,
        });
        if (open.value.name) {
          node.setAttribute('name', open.value.name?.description);
        }
        if (open.value.type) {
          node.setAttribute('type', open.value.type?.description);
        }
        if (names) {
          node.setAttribute('class', names);
        }

        range.surroundContents(node);

        stack = stack.pop();
        ({ open, range, referenceTag } = stack.value);

        range.setEnd(range.endContainer.nextSibling.nextSibling, 0);
      } else {
        break;
      }
    }

    step = tags.next();
  }

  const store = {};

  Object.defineProperty(store, 'selectedRange', {
    set(value) {
      let { 0: start, 1: end } = value;

      let newValue = value;

      if (start && !end) {
        end = store._selectedRange?.[1];
        newValue = [start, end];
      }

      let siblingRange = getCommonParentSiblings(start, end);

      let { 0: leftBound, 1: rightBound } = siblingRange;
      let commonParent =
        leftBound === rightBound || !rightBound
          ? leftBound
          : leftBound?.parentNode || rightBound?.parentNode;

      // are any selected nodes intrinsic

      if (store._selectedSiblingRange) {
        for (let prevEl of siblingsFor(store._selectedSiblingRange)) {
          prevEl.classList.remove('selected');
          let indentClass = [...prevEl.classList.values()].find((val) =>
            val.startsWith('indent-depth-'),
          );
          prevEl.classList.remove(indentClass);

          let prevAnchor = prevEl.previousSibling;
          if (prevAnchor?.tagName === 'A') {
            prevAnchor.remove();
          }
        }
      } else {
        document.getSelection().empty();
      }

      store._selectedRange = newValue;
      store._selectedSiblingRange = siblingRange;
      store._selectedRangeCommonParent = commonParent;

      if (commonParent) {
        let intrinsicSelection = false;

        let indentDepth = Infinity;

        for (let siblingNode of siblingsFor(siblingRange)) {
          intrinsicSelection =
            siblingNode.classList.contains('intrinsic') &&
            !siblingNode.classList.contains('trivia');
          indentDepth = Math.min(indentDepth, countIndents(siblingNode));
          if (intrinsicSelection) break;
        }

        if (intrinsicSelection) {
          store._selectedSiblingRange = [commonParent, commonParent];
        }

        if (!leftBound || !rightBound || intrinsicSelection) {
          commonParent.classList.add('selected');
          commonParent.classList.add('indent-depth-' + countIndents(commonParent));

          let anchor;
          if (commonParent.previousSibling?.tagName === 'A') {
            anchor = commonParent.previousSibling;
          } else {
            anchor = document.createElement('a');
            anchor.style = anchorStyle;
            commonParent.before(anchor);
          }

          let parentRange = document.createRange();

          parentRange.selectNode(commonParent);

          document.getSelection().empty();
          document.getSelection().addRange(parentRange);

          let tooltip = document.createElement('span');
          tooltip.classList.add('tooltip');
          tooltip.prepend(
            printSelfClosingNodeTag(
              buildOpenNodeTag(
                parseNodeFlags(commonParent.classList.contains('token') ? '*' : ''),
                null,
                commonParent.getAttribute('name'),
              ),
            ),
          );
          tooltip.style = `position: absolute; top: -20px`;

          anchor.prepend(tooltip);
        } else {
          for (let siblingNode of siblingsFor(siblingRange)) {
            siblingNode.classList.add('selected');
            siblingNode.classList.add('indent-depth-' + indentDepth);
          }

          let range = document.createRange();

          if (leftBound.compareDocumentPosition(rightBound) === 2) {
            range.setStartBefore(rightBound);
            range.setEndAfter(leftBound);
          } else {
            range.setStartBefore(leftBound);
            range.setEndAfter(rightBound);
          }

          // select siblings
          document.getSelection().empty();
          document.getSelection().addRange(range);
        }
      }
    },

    get() {
      return store._selectedRange;
    },
  });

  Object.defineProperty(store, 'hoverTarget', {
    set(value) {
      let el = value;

      if (store._hoverTarget) {
        let prevEl = store._hoverTarget;
        let anchor = prevEl.previousSibling;
        if (anchor.tagName === 'A') prevEl.parentElement.removeChild(anchor);
      }

      store._hoverTarget = value;

      if (el && !el.classList.contains('selected')) {
        let hover = document.createElement('span');
        hover.classList.add('hover');
        hover.style = `position: absolute; top: 0px`;

        let anchor;
        if (el.previousSibling?.tagName === 'A') {
          anchor = el.previousSibling;
        } else {
          anchor = document.createElement('a');
          anchor.style = anchorStyle;

          el.before(anchor);
        }

        anchor.prepend(hover);
      }
    },

    get() {
      return store._hoverTarget;
    },
  });

  el.addEventListener('mousedown', (e) => {
    // let tokenNode = nodeBindings.get(e.target);

    if (e.target.tagName === 'NODE') {
      store.selectedRange = [e.target, e.target];
    } else {
      store.selectedRange = [null, null];
      document.getSelection().empty();
    }
    store.selectionState = 'selecting';

    if (!store.touchTimeout) {
      e.preventDefault();
    }
  });

  el.addEventListener('mouseover', (e) => {
    if (store.selectionState === 'selecting') {
      let selected = store.selectedRange;

      if (e.relatedTarget?.tagName !== 'NODE') {
        if (e.target?.tagName === 'NODE') {
          let startTokenNode = selected[0];

          if (startTokenNode) {
            range = [startTokenNode, e.target];
          } else {
            range = [e.target, e.target];
          }

          store.selectedRange = range;
        } else {
          store.selectedRange = [selected[0], null];
        }
      }
    }

    if (e.target?.tagName === 'NODE') {
      store.hoverTarget = e.target;
    } else {
      store.hoverTarget = null;
    }
  });

  el.addEventListener('mouseout', (e) => {
    if (store.selectionState === 'selecting') {
      let selected = store.selectedRange;

      if (e.relatedTarget?.tagName === 'NODE') {
        let range;

        let startTokenNode = selected[0];

        if (startTokenNode) {
          range = [startTokenNode, e.relatedTarget];
        } else {
          range = [e.relatedTarget, null];
        }

        store.selectedRange = range;
      } else {
        if (e.relatedTarget?.tagName === 'NODE') {
          store.selectedRange = [store.selectedRange[0], store.selectedRange[0]];
        } else {
          store.selectedRange = [store.selectedRange[0], null];
        }
      }
    }
  });

  addDocumentEventListener('mouseout', (e) => {
    let { target } = e;

    if (store.hoverTarget) {
      let position = target.compareDocumentPosition(el);
      if (!position || position & 0x10) {
        store.hoverTarget = null;
      }
    }
  });

  // addDocumentEventListener('selectionchange', (e) => {
  //   let selection = document.getSelection();

  //   store.hoverTarget = selection.anchorNode;

  //   if (selection.isCollapsed) {
  //     if (!selection.anchorNode || !(selection.anchorNode.compareDocumentPosition(el) & 0x10)) {
  //       store.selectedRange = [null, null];
  //     }
  //   }
  // });

  addDocumentEventListener('mouseup', (e) => {
    store.selectionState = store.selectedRange ? 'selected' : 'none';
    if (e.target.compareDocumentPosition(el) & 0x10) {
      store.selectedRange = [null, null];
      document.getSelection().empty();
      store.selectionState = 'none';
    }
  });

  addDocumentEventListener('mousedown', (e) => {
    if (e.target.compareDocumentPosition(el) & 0x10) {
      store.selectedRange = [null, null];
      store.selectionState = 'none';
    }
  });
}

export const highlightCode = (el, language, matcher = language.defaultMatcher, options) => {
  return new StreamIterable(__highlightCode(el, language, matcher, options));
};

function* __highlightAll(languages, options) {
  let codeBlocks = document.querySelectorAll('code');

  let intersectionChanged = (entries) => {
    for (let entry of entries) {
      let { target } = entry;

      let canonicalURL = target.getAttribute('bablr-lang');
      let language = BMap.get(canonicalURL, languages);
      let flags = target.getAttribute('bablr-ref-flags');

      let name = target.getAttribute('bablr-prod');

      if (!language) continue;
      if (!name && !language.defaultMatcher) continue;

      try {
        evaluateReturn(
          highlightCode(
            target,
            language,
            name ? m`<{printIdentifier(name)}>` : language.defaultMatcher,

            options,
          ),
        );
      } catch (e) {
        console.warn(e);
      }
    }
  };

  let io = new IntersectionObserver(intersectionChanged);

  for (let block of codeBlocks) {
    io.observe(block);
  }
}

export const highlightAll = (languages, options) => {
  return new StreamIterable(__highlightAll(languages, options));
};
