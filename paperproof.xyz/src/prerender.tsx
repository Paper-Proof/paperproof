import React from 'react';
import { renderToString } from 'react-dom/server';
import { readFileSync, writeFileSync } from 'fs';
import { LandingPage } from './landingPage';

const html = renderToString(<LandingPage />);
const template = readFileSync('./public/index.template.html', 'utf-8');
const output = template.replace('<!-- SSR_PLACEHOLDER -->', html);
writeFileSync('./public/index.html', output);
