#!/usr/bin/env python3
"""
Engineering Toolbox Formula Parser
Парсер для извлечения инженерных формул с сайта engineeringtoolbox.com

Этот скрипт обходит сайт engineeringtoolbox.com и извлекает формулы, их описания,
переменные и другую информацию в структурированном формате JSON.

Автор: Makazhan Alpamys, 2025
"""

import requests
from bs4 import BeautifulSoup
import json
import re
import time
import logging
import os
from urllib.parse import urljoin, urlparse
from dataclasses import dataclass, asdict
from typing import List, Dict, Optional, Set, Tuple, Any
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
import threading
from collections import deque
import random
import urllib.robotparser

# OCR dependencies
try:
    import pytesseract
    from PIL import Image
    from io import BytesIO
    OCR_AVAILABLE = True
except ImportError:
    OCR_AVAILABLE = False
    logging.warning("pytesseract or PIL not installed. OCR fallback will not be available.")
    logging.warning("To enable OCR: pip install pytesseract pillow")

# Настройка логирования
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('formula_parser.log', encoding='utf-8'),
        logging.StreamHandler(sys.stdout)
    ]
)
logger = logging.getLogger(__name__)

@dataclass
class Variable:
    """Класс для представления переменной в формуле"""
    symbol: str
    description: str
    unit: Optional[str] = None

@dataclass
class Formula:
    """Структура для хранения инженерной формулы со всеми атрибутами"""
    category: str         # Категория формулы (раздел)
    subcategory: str      # Подкатегория (подраздел)
    formula_name: str     # Название формулы
    formula: str          # Текстовое представление формулы
    description: str      # Описание того, что вычисляет формула
    variables: List[Dict[str, str]]  # Переменные с описаниями и единицами измерения
    url: str              # URL страницы с формулой

class EngineeringFormulaParser:
    """
    Парсер инженерных формул с сайта EngineeringToolbox.com
    
    Основные возможности:
    - Полный обход сайта с извлечением всех формул
    - Обработка текста, HTML-структур и изображений
    - Извлечение переменных, их описаний и единиц измерения
    - Категоризация формул по разделам
    - Сохранение в JSON формате
    """
    
    def __init__(self, base_url="https://www.engineeringtoolbox.com", max_workers=2):
        self.base_url = base_url
        self.session = requests.Session()
        self.user_agent = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
        self.session.headers.update({
            'User-Agent': self.user_agent,
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
            'Accept-Language': 'en-US,en;q=0.5',
            'Connection': 'keep-alive',
            'Cache-Control': 'no-cache'
        })
        
        self.visited_urls: Set[str] = set()
        self.formulas: List[Formula] = []
        self.max_workers = max_workers
        self.lock = threading.Lock()
        
        # Улучшенное управление задержками
        self.min_delay = 1.0  # минимальная задержка в секундах
        self.last_request_time = 0
        
        # Паттерны для извлечения формул из текста
        self.formula_patterns = [
            # Стандартные формулы вида "v = u + a*t" или с индексами "F[total] = m*a"
            r'([A-Za-z][A-Za-z0-9_]*(?:\[\w\s,]+\])?)\s*=\s*([^=\n]+(?:\n[^\w\n=]*[^=\n]*)*?)(?=\n[A-Z]|\n\n|\n\s*where|\n\s*[A-Za-z]+\s*=|$)',
            
            # Формулы с индексами и греческими буквами, например "σ_max = F/A"
            r'([A-Za-z][A-Za-z0-9_]*(?:_\{[^}]+\}|_[A-Za-z0-9]+|\[[^\]]+\])|[αβγδεζηθλμνπρστφχψωΑΒΓΔΕΖΗΘΛΜΝΠΡΣΤΦΧΨΩ][A-Za-z0-9_]*)\s*=\s*([^=\n]+)',
            
            # Формулы после ключевых слов, например "Formula: F = m*a"
            r'(?:Formula|Equation|Calculate):\s*([A-Za-z]\w*)\s*=\s*([^=\n]+)',
            
            # Многострочные формулы
            r'([A-Za-z]\w*)\s*=\s*([^=]+?)(?=\n\s*[A-Z][a-z]+:|$)',
        ]
        
        # Паттерны для извлечения переменных из текста
        self.variable_patterns = [
            # Переменные с "=" и единицами в скобках: "v = скорость (m/s)"
            r'([A-Za-z][A-Za-z0-9_]*)\s*=\s*([^=\n,;]+?)(?:\s*\(([^)]+)\))?(?=\n|,|;|\s*[A-Za-z]\s*=)',
            
            # Переменные с ":" и единицами в скобках: "v: скорость [m/s]"
            r'([A-Za-z][A-Za-z0-9_]*)\s*:\s*([^:\n,;]+?)(?:\s*\[([^\]]+)\])?(?=\n|,|;)',
            
            # Блок переменных после "where"
            r'where[:\s]*\n?((?:\s*[A-Za-z][A-Za-z0-9_]*\s*[=:][^\n]+\n?)+)',
            
            # Однобуквенные переменные: "v - скорость" или "t = время"
            r'\b([A-Za-z])\s*[-=]\s*([^,\n()]+?)(?:\s*\(([^)]+)\))?(?=,|\n|$)',
        ]
        
        # Расширенный список единиц измерения
        self.units = {
            # Длина
            'm', 'mm', 'cm', 'dm', 'km', 'μm', 'nm', 'in', 'ft', 'yd', 'mile', 'mil',
            # Площадь
            'm²', 'm2', 'mm²', 'mm2', 'cm²', 'cm2', 'km²', 'km2', 'in²', 'in2', 'ft²', 'ft2', 'yd²', 'yd2',
            # Объем
            'm³', 'm3', 'L', 'l', 'ml', 'cl', 'dl', 'gal', 'ft³', 'ft3', 'in³', 'in3', 'liter', 'litre',
            # Масса
            'kg', 'g', 'mg', 'μg', 'lb', 'oz', 'ton', 'tonne', 'slug',
            # Время
            's', 'sec', 'min', 'h', 'hr', 'day', 'week', 'month', 'year', 'ms', 'μs', 'ns',
            # Температура
            '°C', '°F', 'K', 'R', 'deg', 'degree', 'celsius', 'fahrenheit', 'kelvin',
            # Давление
            'Pa', 'kPa', 'MPa', 'GPa', 'bar', 'mbar', 'psi', 'psig', 'atm', 'mmHg', 'torr',
            # Энергия
            'J', 'kJ', 'MJ', 'GJ', 'cal', 'kcal', 'BTU', 'kWh', 'MWh', 'eV', 'erg',
            # Мощность
            'W', 'kW', 'MW', 'GW', 'hp', 'BTU/h', 'cal/s', 'PS',
            # Скорость
            'm/s', 'km/h', 'mph', 'ft/s', 'knot', 'mach',
            # Частота
            'Hz', 'kHz', 'MHz', 'GHz', 'THz', 'rpm', 'rps',
            # Электричество
            'V', 'kV', 'MV', 'A', 'mA', 'μA', 'Ω', 'kΩ', 'MΩ', 'F', 'μF', 'nF', 'pF', 'H', 'mH', 'μH',
            # Безразмерные
            'ratio', 'percent', '%', 'ppm', 'ppb', 'ppt', '‰'
        }
        
        # Робот-парсер для проверки robots.txt
        self.robots_parser = self._init_robots_parser()
        
    def _init_robots_parser(self) -> Any:
        """Инициализация парсера robots.txt"""
        robots_parser = urllib.robotparser.RobotFileParser()
        robots_url = urljoin(self.base_url, "/robots.txt")
        try:
            robots_parser.set_url(robots_url)
            robots_parser.read()
            logger.info(f"Загружен robots.txt с {robots_url}")
            # Получаем рекомендуемую задержку из robots.txt, если она указана
            crawl_delay = robots_parser.crawl_delay(self.user_agent) 
            if crawl_delay:
                self.min_delay = max(self.min_delay, crawl_delay)
                logger.info(f"Установлена задержка {self.min_delay} сек. из robots.txt")
            return robots_parser
        except Exception as e:
            logger.warning(f"Не удалось загрузить robots.txt: {e}. Используются стандартные настройки.")
            return None
        
    def can_fetch(self, url: str) -> bool:
        """Проверка, можно ли обращаться к URL согласно robots.txt"""
        if self.robots_parser:
            return self.robots_parser.can_fetch(self.user_agent, url)
        return True  # Если robots.txt недоступен, разрешаем по умолчанию

    def get_page_with_retry(self, url: str, max_retries: int = 3) -> Optional[BeautifulSoup]:
        """Загрузка страницы с повторными попытками при ошибках"""
        # Проверка robots.txt
        if not self.can_fetch(url):
            logger.warning(f"Доступ запрещен правилами robots.txt: {url}")
            return None
            
        for attempt in range(max_retries):
            try:
                # Соблюдаем задержку между запросами
                self._respect_rate_limit()
                
                response = self.session.get(url, timeout=20)
                response.raise_for_status()
                self.last_request_time = time.time()
                
                content_type = response.headers.get('content-type', '')
                if 'text/html' not in content_type:
                    logger.warning(f"Не HTML контент: {url}")
                    return None
                
                return BeautifulSoup(response.content, 'html.parser')
                
            except requests.exceptions.Timeout:
                logger.warning(f"Таймаут для {url}, попытка {attempt + 1}/{max_retries}")
                time.sleep(2 ** attempt + random.uniform(1, 3))
            except requests.exceptions.RequestException as e:
                logger.error(f"Ошибка запроса для {url}: {e}")
                if attempt < max_retries - 1:
                    time.sleep(2 ** attempt + random.uniform(1, 3))
            except Exception as e:
                logger.error(f"Неожиданная ошибка для {url}: {e}")
                break
        
        return None
        
    def _respect_rate_limit(self) -> None:
        """Реализация задержки между запросами"""
        if self.last_request_time > 0:
            elapsed = time.time() - self.last_request_time
            if elapsed < self.min_delay:
                wait_time = self.min_delay - elapsed + random.uniform(0, 0.5)
                time.sleep(wait_time)

    def clean_formula_text(self, text: str) -> str:
        """Очистка и нормализация текста формулы"""
        if not text:
            return ""
        
        # Замена HTML entities
        html_entities = {
            '&alpha;': 'α', '&beta;': 'β', '&gamma;': 'γ', '&delta;': 'δ',
            '&epsilon;': 'ε', '&zeta;': 'ζ', '&eta;': 'η', '&theta;': 'θ',
            '&lambda;': 'λ', '&mu;': 'μ', '&nu;': 'ν', '&pi;': 'π',
            '&rho;': 'ρ', '&sigma;': 'σ', '&tau;': 'τ', '&phi;': 'φ',
            '&chi;': 'χ', '&psi;': 'ψ', '&omega;': 'ω',
            '&Delta;': 'Δ', '&Sigma;': 'Σ', '&Omega;': 'Ω',
            '&plusmn;': '±', '&times;': '×', '&divide;': '÷',
            '&lt;': '<', '&gt;': '>', '&le;': '≤', '&ge;': '≥',
            '&sup2;': '²', '&sup3;': '³', '&radic;': '√',
            '&nbsp;': ' ', '&amp;': '&', '&quot;': '"'
        }
        
        for entity, char in html_entities.items():
            text = text.replace(entity, char)
        
        # Нормализация пробелов
        text = re.sub(r'\s+', ' ', text)
        return text.strip()

    def extract_formulas_from_text(self, text: str, soup: BeautifulSoup = None) -> List[Tuple[str, str]]:
        """Извлечение формул из текста и HTML-структур страницы"""
        formulas = []
        text = self.clean_formula_text(text)
        
        # Извлечение формул из текста по регулярным выражениям
        for pattern in self.formula_patterns:
            matches = re.findall(pattern, text, re.MULTILINE | re.DOTALL)
            for match in matches:
                if isinstance(match, tuple) and len(match) >= 2:
                    left_part = self.clean_formula_text(match[0])
                    right_part = self.clean_formula_text(match[1])
                    
                    if left_part and right_part and len(right_part) > 1:
                        formula = f"{left_part} = {right_part}"
                        if self.is_valid_formula(formula):
                            formulas.append((left_part, formula))
        
        # Если есть DOM, ищем формулы в структуре HTML
        if soup:
            # MathML элементы
            math_elements = soup.find_all(['math', 'mrow', 'mi', 'mo', 'mn'])
            for elem in math_elements:
                text_content = elem.get_text().strip()
                if '=' in text_content:
                    clean_formula = self.clean_formula_text(text_content)
                    if self.is_valid_formula(clean_formula):
                        left_part = clean_formula.split('=')[0].strip()
                        formulas.append((left_part, clean_formula))
            
            # Специальные CSS селекторы для формул
            formula_selectors = [
                '[class*="equation"]', '[class*="formula"]', '[class*="math"]',
                '[id*="equation"]', '[id*="formula"]', '[id*="math"]'
            ]
            
            for selector in formula_selectors:
                elements = soup.select(selector)
                for elem in elements:
                    text_content = elem.get_text().strip()
                    if '=' in text_content:
                        clean_formula = self.clean_formula_text(text_content)
                        if self.is_valid_formula(clean_formula):
                            left_part = clean_formula.split('=')[0].strip()
                            formulas.append((left_part, clean_formula))
            
            # Поиск формул в таблицах
            tables = soup.find_all('table')
            for table in tables:
                cells = table.find_all(['td', 'th'])
                for cell in cells:
                    cell_text = cell.get_text().strip()
                    if '=' in cell_text:
                        cell_formulas = []
                        lines = cell_text.split('\n')
                        for line in lines:
                            if '=' in line and not any(word in line.lower() for word in ['if', 'where', 'then', 'is']):
                                clean_line = self.clean_formula_text(line)
                                if self.is_valid_formula(clean_line):
                                    left_part = clean_line.split('=')[0].strip()
                                    cell_formulas.append((left_part, clean_line))
                        
                        formulas.extend(cell_formulas)
                        
            # Поиск в определениях и списках
            for tag_type in ['dl', 'dd', 'li']:
                elements = soup.find_all(tag_type)
                for elem in elements:
                    elem_text = elem.get_text().strip()
                    if '=' in elem_text and len(elem_text) < 200:
                        lines = elem_text.split('\n')
                        for line in lines:
                            if '=' in line and not any(word in line.lower() for word in ['if', 'where', 'then', 'is']):
                                clean_line = self.clean_formula_text(line)
                                if self.is_valid_formula(clean_line):
                                    left_part = clean_line.split('=')[0].strip()
                                    formulas.append((left_part, clean_line))
            
            # OCR для изображений с формулами
            if OCR_AVAILABLE:
                image_formulas = self.extract_formulas_from_images(soup)
                if image_formulas:
                    formulas.extend(image_formulas)
                    logger.debug(f"Добавлено {len(image_formulas)} формул из изображений через OCR")
        
        return formulas
    
    def extract_formulas_from_images(self, soup: BeautifulSoup) -> List[Tuple[str, str]]:
        """Извлечение формул из изображений с помощью OCR"""
        if not OCR_AVAILABLE:
            return []
            
        formulas = []
        try:
            # Находим изображения, которые могут содержать формулы
            formula_images = []
            
            # Изображения с ключевыми словами в src, alt, class
            img_keywords = ['formula', 'equation', 'math', 'calc']
            for img in soup.find_all('img', src=True):
                img_url = img.get('src', '')
                img_alt = img.get('alt', '')
                img_class = ' '.join(img.get('class', []))
                
                is_formula_image = False
                for keyword in img_keywords:
                    if (keyword in img_url.lower() or 
                        keyword in img_alt.lower() or 
                        keyword in img_class.lower()):
                        is_formula_image = True
                        break
                
                # Также проверяем изображения рядом с формульными ключевыми словами в тексте
                if not is_formula_image:
                    parent_text = img.parent.get_text().lower() if img.parent else ''
                    if any(kw in parent_text for kw in ['formula', 'equation', '=', 'where']):
                        is_formula_image = True
                
                if is_formula_image:
                    formula_images.append(img_url)
            
            # Обрабатываем найденные изображения - без ограничения количества
            for img_url in formula_images:  # Обрабатываем все найденные изображения с формулами
                try:
                    full_img_url = urljoin(self.base_url, img_url)
                    response = self.session.get(full_img_url, stream=True, timeout=10)
                    if response.status_code == 200:
                        img = Image.open(BytesIO(response.content))
                        ocr_text = pytesseract.image_to_string(img, config='--psm 6')
                        
                        # Ищем формульные выражения в OCR тексте
                        ocr_text_clean = self.clean_formula_text(ocr_text)
                        
                        if '=' in ocr_text_clean:
                            for line in ocr_text_clean.split('\n'):
                                if '=' in line:
                                    clean_line = self.clean_formula_text(line)
                                    if self.is_valid_formula(clean_line):
                                        left_part = clean_line.split('=')[0].strip()
                                        formulas.append((left_part, clean_line))
                                        logger.debug(f"OCR формула: {clean_line}")
                except Exception as e:
                    logger.debug(f"Ошибка OCR для {img_url}: {e}")
                    continue
                    
        except Exception as e:
            logger.error(f"Ошибка при обработке изображений: {e}")
        
        return formulas

    def is_valid_formula(self, formula: str) -> bool:
        """Проверка валидности формулы"""
        if not formula or '=' not in formula:
            return False
        
        parts = formula.split('=')
        if len(parts) != 2:
            return False
        
        left, right = parts[0].strip(), parts[1].strip()
        
        # Проверки валидности
        if not left or not right or len(formula) < 5 or len(formula) > 500:
            return False
        
        # Левая часть должна содержать переменную
        if not re.search(r'[A-Za-z]', left):
            return False
        
        # Правая часть должна содержать математические символы
        if not re.search(r'[A-Za-z0-9+\-*/^()√∑∏∫]', right):
            return False
        
        # Исключаем обычный текст
        text_indicators = ['the', 'and', 'or', 'is', 'are', 'can', 'will', 'shall']
        formula_lower = formula.lower()
        for indicator in text_indicators:
            if f' {indicator} ' in formula_lower:
                return False
        
        return True

    def extract_variables_from_text(self, text: str, formula: str) -> List[Variable]:
        """Улучшенное извлечение переменных с поддержкой многосимвольных переменных"""
        variables = []
        
        # УЛУЧШЕНО: Извлечение переменных из формулы с поддержкой многосимвольных переменных
        # Проверим типичные многосимвольные переменные в инженерии
        common_variables = [
            'Re', 'Nu', 'Pr', 'Gr', 'Ra', 'St', 'We', 'Ma', 'Fr', 'Pe', 'Kn',  # Числа подобия
            'rho', 'eta', 'phi', 'psi', 'tau', 'gamma',  # Греческие буквы
            'delta', 'alpha', 'beta', 'sigma', 'omega', 'lambda',
            'COP', 'EER', 'SEER', 'HSPF', 'AFUE', 'MERV',  # Коэффициенты
            'pH', 'rpm', 'ppm', 'MPa', 'GPa', 'kPa',  # Единицы измерения
            'log', 'sin', 'cos', 'tan', 'exp', 'ln'  # Математические функции
        ]
        
        # Базовый поиск однобуквенных и многосимвольных переменных
        formula_vars = set(re.findall(r'\b([A-Za-z][A-Za-z0-9_]*)\b', formula))
        
        # Добавляем поиск известных многосимвольных переменных
        for var in common_variables:
            if var in formula and var not in formula_vars:
                formula_vars.add(var)
        
        # Ищем физические величины с индексами: v_0, T_max
        index_vars = re.findall(r'\b([A-Za-z])_([a-zA-Z0-9]+)\b', formula)
        for base, idx in index_vars:
            var = f"{base}_{idx}"
            if var not in formula_vars:
                formula_vars.add(var)
        
        # Создаем базовые объекты переменных
        for var in formula_vars:
            if len(var) <= 15:  # Увеличиваем максимальную длину переменной
                variables.append(Variable(symbol=var, description="", unit=None))
        
        # Ищем описания переменных в тексте
        for pattern in self.variable_patterns:
            matches = re.findall(pattern, text, re.MULTILINE | re.IGNORECASE | re.DOTALL)
            
            for match in matches:
                if isinstance(match, tuple) and len(match) >= 2:
                    symbol = match[0].strip()
                    description = match[1].strip()
                    unit = match[2].strip() if len(match) > 2 and match[2] else None
                    
                    # Очистка описания
                    description = re.sub(r'\s+', ' ', description).strip()
                    
                    # Определение единицы из описания
                    if not unit:
                        unit = self.extract_unit_from_description(description)
                    
                    # Проверка на многосимвольные переменные
                    # Пример: "Re - Reynolds number" - надо искать "Re", а не "R"
                    matching_symbol = symbol
                    for var_name in formula_vars:
                        # Если найденный символ является частью многосимвольной переменной
                        if var_name.startswith(symbol) and var_name != symbol and len(var_name) <= 5:
                            # Проверяем, что в описании есть эта переменная
                            if var_name.lower() in description.lower() or var_name.lower() in text.lower():
                                matching_symbol = var_name
                                break
                    
                    # Обновляем переменную или добавляем новую
                    existing_var = next((v for v in variables if v.symbol == matching_symbol), None)
                    if existing_var:
                        if description and not existing_var.description:
                            existing_var.description = description
                        if unit and not existing_var.unit:
                            existing_var.unit = unit
                    elif matching_symbol in formula_vars:
                        variables.append(Variable(symbol=matching_symbol, description=description, unit=unit))
        
        # Поиск недостающих описаний в параграфах вокруг формулы
        self._find_missing_variable_descriptions(variables, text, formula)
        
        # Финальная валидация
        validated_variables = []
        for var in variables:
            # Проверяем, что переменная действительно используется в формуле
            if var.symbol in formula_vars or var.symbol in formula:
                # Добавляем описание, если его нет
                if not var.description or len(var.description) < 3:
                    # Улучшенные предположения о стандартных переменных
                    var.description = self._get_standard_variable_description(var.symbol)
                
                # Проверяем и преобразуем единицы измерения
                if var.unit:
                    var.unit = self.validate_unit(var.unit)
                
                validated_variables.append(var)
        
        return validated_variables
    
    def _get_standard_variable_description(self, symbol: str) -> str:
        """Дает стандартное описание для известных физических величин"""
        standard_descriptions = {
            # Числа подобия
            'Re': "Reynolds number",
            'Nu': "Nusselt number",
            'Pr': "Prandtl number",
            'Gr': "Grashof number",
            'Ra': "Rayleigh number",
            'St': "Stanton number",
            'We': "Weber number",
            'Ma': "Mach number",
            'Fr': "Froude number",
            'Pe': "Peclet number",
            'Kn': "Knudsen number",
            
            # Физические величины
            'v': "Velocity",
            'a': "Acceleration",
            'F': "Force",
            'm': "Mass",
            'P': "Power",
            'E': "Energy",
            'Q': "Heat energy",
            'I': "Current",
            'V': "Voltage",
            'R': "Resistance",
            'rho': "Density",
            'T': "Temperature",
            'p': "Pressure",
            't': "Time",
            'h': "Height",
            'l': "Length",
            'w': "Width",
            'd': "Diameter or distance",
            'r': "Radius",
            'A': "Area",
            'Vol': "Volume",
            'f': "Frequency",
            'eta': "Efficiency",
            'mu': "Dynamic viscosity",
            'nu': "Kinematic viscosity",
            'C': "Capacity",
            'c': "Specific heat capacity",
            'k': "Thermal conductivity",
            'g': "Gravitational acceleration",
            'H': "Enthalpy",
            'S': "Entropy",
            'alpha': "Heat transfer coefficient",
            'beta': "Thermal expansion coefficient",
            'lambda': "Wavelength or thermal conductivity",
            'omega': "Angular velocity",
            'tau': "Shear stress",
            'phi': "Phase angle or heat flux",
            
                            # Коэффициенты и константы
                'n': "Count or quantity",
                'EER': "Energy Efficiency Ratio",
                'SEER': "Seasonal Energy Efficiency Ratio",
                'HSPF': "Heating Seasonal Performance Factor",
                'AFUE': "Annual Fuel Utilization Efficiency"
        }
        
        # Проверка на индексированные переменные типа T_max, v_0
        if '_' in symbol:
            base, suffix = symbol.split('_', 1)
            if base in standard_descriptions:
                suffix_descriptions = {
                    '0': "initial",
                    'i': "initial or input",
                    'f': "final",
                    'max': "maximum",
                    'min': "minimum",
                    'avg': "average",
                    'tot': "total",
                    'in': "input or inlet",
                    'out': "output or outlet",
                }
                
                if suffix in suffix_descriptions:
                    return f"{suffix_descriptions[suffix]} {standard_descriptions[base].lower()}"
                return standard_descriptions[base] 
        
        return standard_descriptions.get(symbol, f"Variable {symbol}")
    
    def _find_missing_variable_descriptions(self, variables: List[Variable], text: str, formula: str) -> None:
        """Поиск недостающих описаний переменных в тексте"""
        # Ищем описания в параграфах вокруг формулы
        for var in variables:
            if not var.description or var.description.startswith("Variable "):
                # Ищем упоминание переменной в тексте
                var_pattern = r'\b' + re.escape(var.symbol) + r'\s+(?:is|are|represents|denotes|means|=|-|:|\s+the)\s+([^,.;\n\(\)]+)'
                var_match = re.search(var_pattern, text, re.IGNORECASE)
                if var_match:
                    description = var_match.group(1).strip()
                    if len(description) > 3 and len(description) < 100:
                        var.description = description
                        
                        # Проверяем единицы измерения в скобках/квадратных скобках
                        if not var.unit:
                            unit_match = re.search(r'\(' + re.escape(var.symbol) + r'\s+in\s+([^\)]+)\)', text, re.IGNORECASE)
                            if unit_match:
                                var.unit = self.validate_unit(unit_match.group(1).strip())
                            
                            # Проверяем в квадратных скобках
                            else:
                                unit_match = re.search(r'\[' + re.escape(var.symbol) + r'\]\s*=\s*([^\]]+)\]', text, re.IGNORECASE)
                                if unit_match:
                                    var.unit = self.validate_unit(unit_match.group(1).strip())
                                
                # Если не нашли, проверяем в легендах и примечаниях
                if not var.description or var.description.startswith("Variable "):
                    var_pattern = r'where.*?' + re.escape(var.symbol) + r'[\s=:\-]+([^,;\n\(\)]+)'
                    var_match = re.search(var_pattern, text, re.IGNORECASE)
                    if var_match:
                        description = var_match.group(1).strip()
                        if len(description) > 3 and len(description) < 100:
                            var.description = description

    def extract_unit_from_description(self, description: str) -> Optional[str]:
        """Извлечение единицы измерения из описания"""
        if not description:
            return None
        
        unit_patterns = [
            r'\(([^)]+)\)$',
            r'\[([^\]]+)\]$',
            r'in\s+([A-Za-z²³°/\-]+)',
            r'units?\s*:\s*([A-Za-z²³°/\-]+)',
        ]
        
        for pattern in unit_patterns:
            match = re.search(pattern, description, re.I)
            if match:
                potential_unit = match.group(1).strip()
                validated_unit = self.validate_unit(potential_unit)
                if validated_unit:
                    return validated_unit
        
        return None

    def validate_unit(self, unit: str) -> Optional[str]:
        """Улучшенная валидация единицы измерения с поддержкой составных единиц"""
        if not unit:
            return None
        
        unit = unit.strip()
        
        # Прямое совпадение
        if unit in self.units:
            return unit
        
        # Нечувствительность к регистру
        unit_lower = unit.lower()
        for known_unit in self.units:
            if known_unit.lower() == unit_lower:
                return known_unit
        
        # Нормализация единицы измерения
        normalized_unit = self._normalize_unit(unit)
        if normalized_unit in self.units:
            return normalized_unit
        
        # Составные единицы - более гибкая проверка
        if any(op in unit for op in ['/', '*', '^', '²', '³', '⋅', '·', '-', '(', ')']):
            # Проверка, что в составной единице есть известные базовые единицы
            base_units = self._extract_base_units(unit)
            if base_units:
                # Если длина нормальная и нет странных символов
                if re.match(r'^[A-Za-z0-9²³°/\-\s*^()·⋅.]+$', unit) and len(unit) <= 30:
                    return unit
        
        return None
        
    def _normalize_unit(self, unit: str) -> str:
        """Нормализация записи единицы измерения"""
        # Преобразуем распространенные сокращения
        replacements = {
            'kgs': 'kg·s',
            'ms': 'm/s',
            'mps': 'm/s',
            'fps': 'ft/s',
            'kgf': 'kg·m/s²',
            'nm': 'N·m',
            'kgm': 'kg·m',
            'kgm2': 'kg·m²',
            'kw': 'kW',
            'kwh': 'kWh',
            'kj': 'kJ',
            'mj': 'MJ',
            'sq': 'square',
            'cu': 'cubic',
        }
        
        unit_lower = unit.lower().strip()
        for abbr, full in replacements.items():
            if unit_lower == abbr:
                return full
        
        # Удаляем пробелы для лучшего сопоставления
        unit = re.sub(r'\s+', '', unit)
        
        # Преобразуем символы
        unit = unit.replace('**', '^').replace('sq.', '²').replace('cu.', '³')
        
        # Заменяем распространенные описательные формы на символы
        unit = re.sub(r'square([A-Za-z])', r'\1²', unit, flags=re.IGNORECASE)
        unit = re.sub(r'cubic([A-Za-z])', r'\1³', unit, flags=re.IGNORECASE)
        
        return unit
        
    def _extract_base_units(self, compound_unit: str) -> List[str]:
        """Извлечение базовых единиц измерения из составной единицы"""
        base_units = []
        
        # Разделяем составную единицу на базовые
        clean_unit = re.sub(r'[²³^*/()·⋅\s]', ' ', compound_unit)
        potential_units = clean_unit.split()
        
        for part in potential_units:
            part = part.strip()
            if not part:
                continue
                
            # Убираем цифры и символы из потенциальной единицы
            clean_part = re.sub(r'[^A-Za-z]', '', part)
            
            # Проверяем, есть ли эта единица в списке известных
            if clean_part in self.units:
                base_units.append(clean_part)
            else:
                # Проверяем с учетом регистра
                for known_unit in self.units:
                    if known_unit.lower() == clean_part.lower():
                        base_units.append(known_unit)
                        break
        
        return base_units

    def extract_category_info(self, soup: BeautifulSoup, url: str) -> Tuple[str, str]:
        """Извлечение категории и подкатегории"""
        category = "General"
        subcategory = "Unknown"
        
        try:
            # Анализ URL
            url_path = urlparse(url).path
            path_parts = [part for part in url_path.split('/') if part and not part.endswith('.html')]
            
            if len(path_parts) >= 1:
                category = path_parts[0].replace('-', ' ').title()
            if len(path_parts) >= 2:
                subcategory = path_parts[1].replace('-', ' ').title()
            
            # Анализ breadcrumbs
            breadcrumb_selectors = ['.breadcrumb', '.breadcrumbs', 'nav[aria-label*="breadcrumb"]']
            for selector in breadcrumb_selectors:
                breadcrumb = soup.select_one(selector)
                if breadcrumb:
                    links = breadcrumb.find_all('a')
                    if len(links) >= 2:
                        category = links[1].get_text().strip()
                        if len(links) >= 3:
                            subcategory = links[2].get_text().strip()
                        break
            
            # Анализ заголовка
            title = soup.find('title')
            if title and category == "General":
                title_text = title.get_text().strip()
                if ' - ' in title_text:
                    parts = title_text.split(' - ')
                    if len(parts) >= 2:
                        category = parts[0].strip()
                        subcategory = parts[1].strip()
            
            # Очистка
            category = re.sub(r'[^\w\s-]', '', category).strip()
            subcategory = re.sub(r'[^\w\s-]', '', subcategory).strip()
            
            if not category or len(category) > 50:
                category = "General"
            if not subcategory or len(subcategory) > 50:
                subcategory = "Unknown"
                
        except Exception as e:
            logger.debug(f"Ошибка извлечения категории для {url}: {e}")
        
        return category, subcategory

    def extract_description(self, soup: BeautifulSoup, formula_name: str, formula_text: str) -> str:
        """Извлечение описания формулы"""
        description = ""
        
        try:
            # Поиск в заголовках и следующих параграфах
            headers = soup.find_all(['h1', 'h2', 'h3', 'h4', 'h5', 'h6'])
            for header in headers:
                header_text = header.get_text().strip()
                if any(keyword in header_text.lower() for keyword in ['formula', 'equation', 'calculation']):
                    next_p = header.find_next('p')
                    if next_p:
                        desc_text = next_p.get_text().strip()
                        if 20 < len(desc_text) < 300:
                            description = desc_text
                            break
            
            # Поиск рядом с формулой
            if not description:
                page_text = soup.get_text()
                formula_pattern = re.escape(formula_text[:30])
                pattern = rf'(.{{0,200}}){formula_pattern}(.{{0,200}})'
                match = re.search(pattern, page_text, re.IGNORECASE | re.DOTALL)
                
                if match:
                    after_text = match.group(2).strip()
                    sentences = after_text.split('.')
                    for sentence in sentences:
                        sentence = sentence.strip()
                        if (20 < len(sentence) < 200 and
                            any(keyword in sentence.lower() for keyword in 
                                ['calculates', 'determines', 'computes', 'formula', 'used to'])):
                            description = sentence
                            break
            
            # Meta описание
            if not description:
                meta_desc = soup.find('meta', attrs={'name': 'description'})
                if meta_desc:
                    desc_content = meta_desc.get('content', '').strip()
                    if 20 < len(desc_content) < 300:
                        description = desc_content
            
            # Первый параграф
            if not description:
                first_p = soup.find('p')
                if first_p:
                    p_text = first_p.get_text().strip()
                    if 20 < len(p_text) < 300:
                        description = p_text
            
            # По умолчанию
            if not description:
                description = f"Engineering formula for calculating {formula_name.lower()}" if formula_name else "Engineering calculation formula"
            
            # Очистка
            description = re.sub(r'\s+', ' ', description).strip()
            description = re.sub(r'[^\w\s.,()-]', '', description)
            
        except Exception as e:
            logger.debug(f"Ошибка извлечения описания: {e}")
            description = "Engineering calculation formula"
        
        return description[:500]

    def generate_formula_name(self, formula_text: str, page_title: str, category: str) -> str:
        """Улучшенная генерация названия формулы с контекстным анализом"""
        try:
            # Словарь для более обширного сопоставления символов с названиями физических величин
            standard_names = {
                # Основные величины
                'v': 'Velocity', 'V': 'Volume', 'f': 'Force', 'F': 'Force', 
                'p': 'Pressure', 'P': 'Power', 'e': 'Energy', 'E': 'Energy',
                'q': 'Flow Rate', 'Q': 'Heat', 'a': 'Acceleration', 't': 'Time', 
                'd': 'Distance', 'D': 'Diameter', 'w': 'Work', 'W': 'Work',
                'h': 'Height', 'H': 'Enthalpy', 'r': 'Radius', 'R': 'Resistance',
                'm': 'Mass', 'M': 'Mass', 'n': 'Number', 'N': 'Force', 
                'A': 'Area', 'I': 'Current', 'C': 'Capacitance', 'L': 'Inductance',
                
                # Числа подобия и коэффициенты
                'Re': 'Reynolds Number', 'Nu': 'Nusselt Number', 'Pr': 'Prandtl Number',
                'Ra': 'Rayleigh Number', 'Gr': 'Grashof Number', 'Pe': 'Peclet Number',
                'St': 'Stanton Number', 'Sh': 'Sherwood Number', 'Sc': 'Schmidt Number',
                'We': 'Weber Number', 'Fr': 'Froude Number', 'Ma': 'Mach Number',
                'K': 'Heat Transfer Coefficient', 'U': 'Overall Heat Transfer Coefficient',
                'eta': 'Efficiency', 'COP': 'Coefficient of Performance',
                'alpha': 'Heat Transfer Coefficient', 'beta': 'Expansion Coefficient',
                'rho': 'Density', 'lambda': 'Thermal Conductivity',
                
                # Мультисимвольные переменные 
                'cp': 'Specific Heat Capacity', 'cv': 'Specific Heat Capacity',
                'nu': 'Kinematic Viscosity', 'mu': 'Dynamic Viscosity',
                'PV': 'Present Value', 'FV': 'Future Value', 'NPV': 'Net Present Value',
                'ROI': 'Return on Investment', 'IRR': 'Internal Rate of Return',
                'COP': 'Coefficient of Performance', 'EER': 'Energy Efficiency Ratio',
                'SHF': 'Sensible Heat Factor', 'DT': 'Temperature Difference',
                'DP': 'Pressure Difference', 'pH': 'pH Value', 
                'EF': 'Emission Factor', 'GWP': 'Global Warming Potential'
            }
            
            # Словарь для контекстных названий формул
            context_formulas = {
                # Механика
                'F=ma': 'Newton\'s Second Law', 
                'F=G*m*M': 'Gravitational Force',
                'KE=0.5*m*v': 'Kinetic Energy', 'KE=0.5*m*v^2': 'Kinetic Energy',
                'PE=mgh': 'Potential Energy', 'E=mc2': 'Einstein\'s Energy-Mass Equivalence',
                'p=mv': 'Momentum', 'F=dp/dt': 'Force as Change in Momentum',
                'W=F*d': 'Work', 'P=W/t': 'Power',
                
                # Термодинамика
                'PV=nRT': 'Ideal Gas Law', 'Q=mc∆T': 'Heat Energy',
                'COP=Q/W': 'Coefficient of Performance', 'η=W/Q': 'Thermal Efficiency',
                'Q=U*A*∆T': 'Heat Transfer Rate', 'h=Q/(A*∆T)': 'Heat Transfer Coefficient',
                
                # Гидродинамика
                'Re=ρvD/μ': 'Reynolds Number', 'Nu=hL/k': 'Nusselt Number',
                'Δp=f*(L/D)*(ρv²/2)': 'Darcy-Weisbach Equation', 'Q=VA': 'Flow Rate',
                
                # Электричество
                'V=IR': 'Ohm\'s Law', 'P=VI': 'Electrical Power',
                'E=IR': 'Voltage', 'R=ρL/A': 'Resistance',
                
                # Экономика
                'ROI=(Gain-Cost)/Cost': 'Return on Investment',
                'NPV=Σ[CFt/(1+r)^t]': 'Net Present Value'
            }
            
            # 1. Попробуем распознать известную формулу
            clean_formula = re.sub(r'\s+', '', formula_text.lower())
            for formula_pattern, name in context_formulas.items():
                pattern = re.sub(r'\s+', '', formula_pattern.lower())
                if clean_formula.startswith(pattern.split('=')[0]) and '=' in clean_formula:
                    return name
                    
            # 2. Анализируем левую часть формулы
            if '=' in formula_text:
                left_part = formula_text.split('=')[0].strip()
                clean_left = re.sub(r'[_\[\]{}]', '', left_part)
                
                # Проверяем известные переменные в левой части
                if 0 < len(clean_left) <= 20:
                    for var, name in standard_names.items():
                        # Полное совпадение или переменная с индексом
                        if clean_left == var or clean_left.startswith(f"{var}_") or clean_left.startswith(f"{var}["):
                            return f"{name} Formula"
            
            # 3. Ищем ключевые слова в заголовке страницы
            physical_terms = [
                'velocity', 'pressure', 'force', 'energy', 'power', 'heat', 'flow', 'mass', 
                'temperature', 'acceleration', 'friction', 'resistance', 'conductivity', 'efficiency',
                'stress', 'strain', 'elasticity', 'viscosity', 'density', 'concentration', 'entropy',
                'enthalpy', 'specific', 'thermal', 'electric', 'magnetic', 'radiation', 'conversion',
                'diffusion', 'sound', 'light', 'wave', 'fluid', 'gas', 'solid', 'calculation',
                'coefficient', 'factor', 'number'
            ]
            
            # Более умный анализ заголовка страницы
            title_lower = page_title.lower()
            for term in physical_terms:
                if term in title_lower:
                    # Находим контекстные слова вокруг термина
                    match = re.search(r'((\w+\s+){0,2}' + re.escape(term) + r'(\s+\w+){0,2})', title_lower)
                    if match:
                        return match.group(1).title() + " Formula"
                
            # 4. Используем первые значимые слова из заголовка страницы
            title_words = page_title.split()
            meaningful_words = [word for word in title_words 
                              if len(word) > 3 and word.lower() not in 
                              ['the', 'and', 'for', 'with', 'engineering', 'toolbox', 'formula', 
                               'equation', 'calculation', 'calculate', 'how', 'what']]
            
            if meaningful_words:
                return " ".join(meaningful_words[:3]).title() + " Formula"
            
            # 5. Используем категорию в последнюю очередь
            if category and category != "General":
                return f"{category} Formula"
            
            # Если все методы не дали результата
            return "Engineering Formula"
            
        except Exception as e:
            logger.debug(f"Ошибка генерации названия: {e}")
            return "Engineering Formula"

    def get_all_internal_links(self, soup: BeautifulSoup, current_url: str) -> Set[str]:
        """ИСПРАВЛЕННЫЙ метод получения всех внутренних ссылок"""
        links = set()
        
        if not soup:
            return links
        
        try:
            # Находим все ссылки на странице
            for link in soup.find_all('a', href=True):
                href = link.get('href')
                if not href:
                    continue
                
                # Преобразуем в абсолютную ссылку
                full_url = urljoin(current_url, href)
                parsed = urlparse(full_url)
                
                # Проверяем домен
                base_domain = urlparse(self.base_url).netloc
                if parsed.netloc != base_domain:
                    continue
                
                # Исключаем файлы и нежелательные ссылки
                excluded_extensions = ['.jpg', '.jpeg', '.png', '.gif', '.svg', '.ico',
                                     '.css', '.js', '.pdf', '.doc', '.docx', '.xls', 
                                     '.xlsx', '.zip', '.rar', '.tar', '.gz']
                
                path_lower = parsed.path.lower()
                if any(path_lower.endswith(ext) for ext in excluded_extensions):
                    continue
                
                # Исключаем якоря на той же странице
                if parsed.path == urlparse(current_url).path and parsed.fragment:
                    continue
                
                # Исключаем спецссылки
                if any(protocol in full_url for protocol in ['mailto:', 'tel:', 'javascript:']):
                    continue
                
                # Нормализуем URL
                normalized_url = f"{parsed.scheme}://{parsed.netloc}{parsed.path}"
                if normalized_url.endswith('/'):
                    normalized_url = normalized_url.rstrip('/')
                
                links.add(normalized_url)
            
            logger.debug(f"Найдено {len(links)} ссылок на странице {current_url}")
            
        except Exception as e:
            logger.error(f"Ошибка получения ссылок с {current_url}: {e}")
        
        return links

    def crawl_single_page(self, url: str) -> List[Formula]:
        """ИСПРАВЛЕННЫЙ метод обработки одной страницы с улучшенной структурой"""
        # Проверяем, не посещали ли мы уже эту страницу
        with self.lock:
            if url in self.visited_urls:
                return []
            self.visited_urls.add(url)
        
        logger.info(f"Парсим страницу: {url}")
        
        # Получаем содержимое страницы
        soup = self.get_page_with_retry(url)
        if not soup:
            logger.warning(f"Не удалось получить страницу: {url}")
            return []
        
        formulas_found = []
        try:
            # Получаем базовую информацию о странице
            page_info = self._get_page_info(soup, url)
            
            # Извлекаем формулы
            formula_candidates = self._extract_formula_candidates(soup)
            
            # Обрабатываем найденные формулы
            formulas_found = self._process_formula_candidates(formula_candidates, soup, page_info)
            
        except Exception as e:
            logger.error(f"Ошибка обработки страницы {url}: {e}")
        
        logger.debug(f"Страница {url} обработана, найдено {len(formulas_found)} формул")
        return formulas_found
    
    def _get_page_info(self, soup: BeautifulSoup, url: str) -> Dict:
        """Извлечение базовой информации о странице"""
        category, subcategory = self.extract_category_info(soup, url)
        title_elem = soup.find('title')
        page_title = title_elem.text.strip() if title_elem else "Unknown Page"
        page_text = soup.get_text()
        
        return {
            'category': category,
            'subcategory': subcategory,
            'page_title': page_title,
            'page_text': page_text,
            'url': url
        }
    
    def _extract_formula_candidates(self, soup: BeautifulSoup) -> List[Tuple[str, str]]:
        """Извлечение кандидатов формул со страницы"""
        page_text = soup.get_text()
        formula_candidates = self.extract_formulas_from_text(page_text, soup)
        logger.debug(f"Найдено {len(formula_candidates)} кандидатов формул")
        return formula_candidates
    
    def _process_formula_candidates(self, formula_candidates: List[Tuple[str, str]], 
                                   soup: BeautifulSoup, page_info: Dict) -> List[Formula]:
        """Обработка кандидатов формул и создание объектов Formula"""
        formulas_found = []
        page_text = page_info['page_text']
        url = page_info['url']
        
        for formula_name_candidate, formula_text in formula_candidates:
            try:
                # Генерируем данные формулы
                formula_name = self.generate_formula_name(
                    formula_text, 
                    page_info['page_title'], 
                    page_info['category']
                )
                description = self.extract_description(soup, formula_name_candidate, formula_text)
                variables = self.extract_variables_from_text(page_text, formula_text)
                
                # Преобразуем переменные в JSON формат
                variables_dict = self._convert_variables_to_dict(variables)
                
                # Создаем объект формулы
                formula = Formula(
                    category=page_info['category'],
                    subcategory=page_info['subcategory'],
                    formula_name=formula_name,
                    formula=formula_text,
                    description=description,
                    variables=variables_dict,
                    url=url
                )
                
                formulas_found.append(formula)
                logger.info(f"Найдена формула '{formula_name}': {formula_text[:50]}...")
                
            except Exception as e:
                logger.error(f"Ошибка обработки формулы на {url}: {e}")
                continue
                
        return formulas_found
    
    def _convert_variables_to_dict(self, variables: List[Variable]) -> List[Dict]:
        """Преобразование объектов Variable в словари для JSON"""
        variables_dict = []
        for var in variables:
            var_dict = {
                "symbol": var.symbol,
                "description": var.description or f"Variable {var.symbol}",
            }
            if var.unit:
                var_dict["unit"] = var.unit
            variables_dict.append(var_dict)
            
        return variables_dict

    def crawl_website_systematically(self, start_url: str = None, max_pages: int = 2000) -> List[Formula]:
        """УЛУЧШЕННЫЙ системный обход всего сайта с точной статистикой"""
        if not start_url:
            start_url = self.base_url
        
        logger.info("="*60)
        logger.info("НАЧАЛО СИСТЕМНОГО ОБХОДА САЙТА")
        logger.info(f"Стартовый URL: {start_url}")
        logger.info(f"Максимум страниц: {max_pages}")
        logger.info("="*60)
        
        # Улучшенный трекинг статистики
        stats = {
            'processed_pages': 0,          # Число обработанных страниц
            'pages_with_formulas': 0,      # Страницы, на которых найдены формулы
            'formulas_found': 0,           # Общее число найденных формул
            'ocr_formulas': 0,             # Формулы, найденные через OCR
            'errors': 0,                   # Ошибки при обработке страниц
            'robots_blocked': 0            # Страницы, заблокированные robots.txt
        }
        
        # Очередь URL для обхода
        urls_queue = deque([start_url])
        
        # Получаем начальные ссылки с главной страницы
        logger.info("Собираем начальные ссылки с главной страницы...")
        main_soup = self.get_page_with_retry(start_url)
        if main_soup:
            main_links = self.get_all_internal_links(main_soup, start_url)
            urls_queue.extend(main_links)
            logger.info(f"Добавлено {len(main_links)} начальных ссылок в очередь")
        else:
            logger.error("Не удалось получить главную страницу!")
            return []
        
        # Основной цикл обхода
        while urls_queue and stats['processed_pages'] < max_pages:
            # Берем пакет URL для параллельной обработки
            batch_size = min(self.max_workers, len(urls_queue))
            current_batch = []
            
            for _ in range(batch_size):
                if urls_queue:
                    url = urls_queue.popleft()
                    # Проверка robots.txt
                    if not self.can_fetch(url):
                        with self.lock:
                            stats['robots_blocked'] += 1
                        continue
                    current_batch.append(url)
            
            if not current_batch:
                continue
            
            # Параллельная обработка пакета
            with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
                future_to_url = {
                    executor.submit(self.crawl_single_page, url): url 
                    for url in current_batch
                }
                
                for future in as_completed(future_to_url):
                    url = future_to_url[future]
                    try:
                        page_formulas = future.result(timeout=60)
                        
                        # Обновляем статистику и сохраняем формулы
                        with self.lock:
                            self.formulas.extend(page_formulas)
                            stats['processed_pages'] += 1
                            stats['formulas_found'] += len(page_formulas)
                            
                            if page_formulas:
                                stats['pages_with_formulas'] += 1
                        
                        # Если на странице есть формулы, получаем с неё дополнительные ссылки
                        if page_formulas or self.is_formula_related_page(url):
                            try:
                                soup = self.get_page_with_retry(url)
                                if soup:
                                    new_links = self.get_all_internal_links(soup, url)
                                    # Добавляем только непосещённые ссылки
                                    with self.lock:
                                        for link in new_links:
                                            if link not in self.visited_urls and link not in urls_queue:
                                                urls_queue.append(link)
                            except Exception as e:
                                logger.debug(f"Ошибка получения доп. ссылок с {url}: {e}")
                        
                        if page_formulas:
                            logger.info(f"Найдено {len(page_formulas)} формул на {url}")
                        
                    except TimeoutError:
                        logger.warning(f"Таймаут при обработке {url}")
                        with self.lock:
                            stats['processed_pages'] += 1
                            stats['errors'] += 1
                    except Exception as e:
                        logger.error(f"Ошибка обработки {url}: {e}")
                        with self.lock:
                            stats['processed_pages'] += 1
                            stats['errors'] += 1
            
            # Периодический отчёт о прогрессе
            if stats['processed_pages'] % 50 == 0 and stats['processed_pages'] > 0:
                logger.info("-" * 50)
                logger.info(f"ПРОГРЕСС: {stats['processed_pages']}/{max_pages} страниц обработано")
                logger.info(f"Страниц с формулами: {stats['pages_with_formulas']} ({(stats['pages_with_formulas']/stats['processed_pages']*100):.1f}%)")
                logger.info(f"Всего найдено формул: {stats['formulas_found']} (в среднем {(stats['formulas_found']/stats['pages_with_formulas'] if stats['pages_with_formulas'] > 0 else 0):.1f} на страницу)")
                logger.info(f"Ссылок в очереди: {len(urls_queue)}")
                logger.info(f"Ошибки: {stats['errors']}, Заблокировано robots.txt: {stats['robots_blocked']}")
                logger.info("-" * 50)
                
                # Сохраняем промежуточные результаты каждые 500 страниц
                if stats['processed_pages'] % 500 == 0 and len(self.formulas) > 0:
                    self.save_formulas_to_json(f"engineering_formulas_progress_{stats['processed_pages']}.json")
                    logger.info(f"Промежуточные результаты сохранены в engineering_formulas_progress_{stats['processed_pages']}.json")
        
        logger.info("="*60)
        logger.info("ОБХОД САЙТА ЗАВЕРШЁН!")
        logger.info(f"Всего обработано страниц: {stats['processed_pages']}")
        logger.info(f"Страниц с формулами: {stats['pages_with_formulas']} ({(stats['pages_with_formulas']/stats['processed_pages']*100 if stats['processed_pages'] > 0 else 0):.1f}%)")
        logger.info(f"Всего найдено формул: {stats['formulas_found']}")
        logger.info(f"Ошибки: {stats['errors']}, Заблокировано robots.txt: {stats['robots_blocked']}")
        logger.info("="*60)
        
        return self.formulas

    def is_formula_related_page(self, url: str) -> bool:
        """Проверка, связана ли страница с формулами"""
        formula_keywords = [
            'formula', 'equation', 'calculation', 'calculator', 'compute',
            'calculate', 'physics', 'mechanics', 'thermodynamics', 'fluid',
            'engineering', 'math', 'mathematical'
        ]
        url_lower = url.lower()
        return any(keyword in url_lower for keyword in formula_keywords)

    def remove_duplicate_formulas(self):
        """Удаление дублирующихся формул"""
        seen_formulas = set()
        unique_formulas = []
        
        for formula in self.formulas:
            # Создаем нормализованный ключ для сравнения
            normalized = re.sub(r'\s+', ' ', formula.formula.lower().strip())
            normalized = re.sub(r'[^\w\s=+\-*/()^]', '', normalized)
            
            if normalized not in seen_formulas and len(normalized) > 3:
                seen_formulas.add(normalized)
                unique_formulas.append(formula)
        
        removed_count = len(self.formulas) - len(unique_formulas)
        self.formulas = unique_formulas
        
        if removed_count > 0:
            logger.info(f"Удалено {removed_count} дублирующихся формул")

    def save_formulas_to_json(self, filename: str = "engineering_formulas_complete.json"):
        """Сохранение формул в JSON в соответствии с требованиями задачи"""
        # Удаляем дубликаты
        self.remove_duplicate_formulas()
        
        # Сортируем для лучшей организации
        self.formulas.sort(key=lambda x: (x.category, x.subcategory, x.formula_name))
        
        # Преобразуем в список словарей для JSON
        formulas_data = []
        for formula in self.formulas:
            formula_dict = asdict(formula)
            formulas_data.append(formula_dict)
        
        # Сохраняем
        try:
            with open(filename, 'w', encoding='utf-8') as f:
                json.dump(formulas_data, f, indent=2, ensure_ascii=False)
            
            logger.info("="*60)
            logger.info("РЕЗУЛЬТАТЫ СОХРАНЕНЫ!")
            logger.info(f"Файл: {filename}")
            logger.info(f"Всего формул: {len(formulas_data)}")
            logger.info("="*60)
            
        except Exception as e:
            logger.error(f"Ошибка сохранения {filename}: {e}")

    def generate_statistics(self) -> Dict:
        """Генерация подробной статистики"""
        if not self.formulas:
            return {"error": "Формулы не найдены"}
        
        categories = {}
        subcategories = {}
        total_variables = 0
        formulas_with_units = 0
        formulas_with_descriptions = 0
        
        for formula in self.formulas:
            # Статистика категорий
            categories[formula.category] = categories.get(formula.category, 0) + 1
            subcat_key = f"{formula.category}/{formula.subcategory}"
            subcategories[subcat_key] = subcategories.get(subcat_key, 0) + 1
            
            # Статистика переменных
            total_variables += len(formula.variables)
            
            # Статистика покрытия данных
            if any('unit' in var for var in formula.variables):
                formulas_with_units += 1
            
            if formula.description and len(formula.description.strip()) > 10:
                formulas_with_descriptions += 1
        
        return {
            "total_formulas": len(self.formulas),
            "total_variables": total_variables,
            "avg_variables_per_formula": round(total_variables / len(self.formulas), 2),
            "categories_count": len(categories),
            "categories": dict(sorted(categories.items(), key=lambda x: x[1], reverse=True)),
            "subcategories_count": len(subcategories),
            "top_subcategories": dict(sorted(subcategories.items(), key=lambda x: x[1], reverse=True)[:15]),
            "formulas_with_units": formulas_with_units,
            "formulas_with_descriptions": formulas_with_descriptions,
            "coverage_percentage": {
                "units": f"{(formulas_with_units/len(self.formulas)*100):.1f}%",
                "descriptions": f"{(formulas_with_descriptions/len(self.formulas)*100):.1f}%"
            }
        }

def main():
    """Запуск парсера инженерных формул"""
    import argparse
    
    # CLI аргументы
    arg_parser = argparse.ArgumentParser(
        description="Парсер инженерных формул с сайта EngineeringToolbox.com",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    
    # Добавление всех возможных опций
    arg_parser.add_argument(
        '--start-url', 
        default='https://www.engineeringtoolbox.com',
        help="URL с которого начать обход"
    )
    
    arg_parser.add_argument(
        '--max-pages', 
        type=int, 
        default=1500,
        help="Лимит страниц для обработки"
    )
    
    arg_parser.add_argument(
        '--output', 
        default="engineering_formulas_complete.json",
        help="Файл для сохранения результатов"
    )
    
    arg_parser.add_argument(
        '--threads', 
        type=int, 
        default=2,
        help="Число параллельных потоков"
    )
    
    arg_parser.add_argument(
        '--resume', 
        action='store_true',
        help="Продолжить предыдущий парсинг"
    )
    
    arg_parser.add_argument(
        '--log-level', 
        choices=['DEBUG', 'INFO', 'WARNING', 'ERROR'], 
        default='INFO',
        help="Уровень логирования"
    )
    
    arg_parser.add_argument(
        '--debug', 
        action='store_true',
        help="Режим отладки"
    )
    
    arg_parser.add_argument(
        '--examples', 
        type=int, 
        default=5,
        help="Число примеров в отчете"
    )
    
    args = arg_parser.parse_args()
    
    # Настройка логов
    if args.debug:
        logger.setLevel(logging.DEBUG)
    else:
        logger.setLevel(getattr(logging, args.log_level))
    
    print("="*70)
    print("ENGINEERING TOOLBOX FORMULA PARSER")
    print("Парсер инженерных формул с полным соответствием техническому заданию")
    print("="*70)
    print(f"Стартовый URL: {args.start_url}")
    print(f"Максимум страниц: {args.max_pages}")
    print(f"Выходной файл: {args.output}")
    print(f"Количество потоков: {args.threads}")
    if args.resume:
        print("Режим: продолжение предыдущей сессии")
    print("="*70)
    
    # Инициализация парсера
    parser = EngineeringFormulaParser(base_url=args.start_url, max_workers=args.threads)
    
    # Восстановление предыдущей сессии
    if args.resume and os.path.exists(args.output):
        try:
            with open(args.output, 'r', encoding='utf-8') as f:
                previous_data = json.load(f)
                
            # Восстанавливаем формулы из предыдущей сессии
            for formula_dict in previous_data:
                formula = Formula(
                    category=formula_dict['category'],
                    subcategory=formula_dict['subcategory'],
                    formula_name=formula_dict['formula_name'],
                    formula=formula_dict['formula'],
                    description=formula_dict['description'],
                    variables=formula_dict['variables'],
                    url=formula_dict['url']
                )
                parser.formulas.append(formula)
                # Добавляем URL в список посещенных
                parser.visited_urls.add(formula_dict['url'])
                
            print(f"Восстановлено {len(parser.formulas)} формул из предыдущей сессии.")
            print(f"Добавлено {len(parser.visited_urls)} URL в список посещённых.")
            
        except Exception as e:
            print(f"Ошибка восстановления предыдущей сессии: {e}")
            print("Запуск с чистого листа...")
    
    try:
        # Засекаем время
        start_time = time.time()
        
        # Запускаем полный обход сайта
        logger.info("Запуск системного обхода сайта engineeringtoolbox.com...")
        formulas = parser.crawl_website_systematically(
            start_url=args.start_url, 
            max_pages=args.max_pages
        )
        
        end_time = time.time()
        execution_time = end_time - start_time
        
        # Сохраняем результаты
        parser.save_formulas_to_json(args.output)
        
        # Генерируем и выводим статистику
        stats = parser.generate_statistics()
        
        print("\n" + "="*70)
        print("ФИНАЛЬНАЯ СТАТИСТИКА ПАРСИНГА:")
        print("="*70)
        
        print(f"Время выполнения: {execution_time:.2f} секунд")
        
        # Проверяем наличие ошибки в статистике (нет формул)
        if "error" in stats:
            print(f"Статус: {stats['error']}")
            print(f"Обработано страниц: {args.max_pages}")
            
            # Пропускаем вывод статистики по формулам и переходим к завершению
            print("\n" + "="*70)
            print("ПАРСИНГ ЗАВЕРШЁН!")
            print(f"Результат сохранён в файл: {args.output}")
            print("="*70)
            return
            
        # Если формулы найдены, выводим полную статистику
        print(f"Всего формул извлечено: {stats['total_formulas']}")
        print(f"Всего переменных: {stats['total_variables']}")
        print(f"Среднее количество переменных на формулу: {stats['avg_variables_per_formula']}")
        print(f"Количество категорий: {stats['categories_count']}")
        print(f"Количество подкатегорий: {stats['subcategories_count']}")
        print(f"Формулы с единицами измерения: {stats['coverage_percentage']['units']}")
        print(f"Формулы с описаниями: {stats['coverage_percentage']['descriptions']}")
        
        print("\nТОП-10 КАТЕГОРИЙ:")
        for i, (category, count) in enumerate(list(stats['categories'].items())[:10], 1):
            print(f"  {i}. {category}: {count} формул")
        
        print("\nТОП-10 ПОДКАТЕГОРИЙ:")
        for i, (subcategory, count) in enumerate(list(stats['top_subcategories'].items())[:10], 1):
            print(f"  {i}. {subcategory}: {count} формул")
        
        # Примеры найденных формул
        if args.examples > 0:
            print("\n" + "="*70)
            print("ПРИМЕРЫ НАЙДЕННЫХ ФОРМУЛ:")
            print("="*70)
            
            examples = []
            seen_categories = set()
            for formula in formulas:
                if formula.category not in seen_categories and len(examples) < args.examples:
                    examples.append(formula)
                    seen_categories.add(formula.category)
            
            for i, formula in enumerate(examples, 1):
                print(f"\n{i}. ФОРМУЛА: {formula.formula_name}")
                print(f"   Формула: {formula.formula}")
                print(f"   Описание: {formula.description[:100]}...")
                print(f"   Категория: {formula.category} → {formula.subcategory}")
                print(f"   Переменных: {len(formula.variables)}")
                print(f"   URL: {formula.url}")
                
                if formula.variables:
                    print("   Переменные:")
                    for var in formula.variables[:3]:  # Первые 3
                        unit_text = f" [{var.get('unit', 'единица не указана')}]" if var.get('unit') else ""
                        print(f"     • {var['symbol']}: {var['description']}{unit_text}")
                    if len(formula.variables) > 3:
                        print(f"     ... и ещё {len(formula.variables) - 3} переменных")
        
        print("\n" + "="*70)
        print("ПАРСИНГ УСПЕШНО ЗАВЕРШЁН!")
        print(f"Результат сохранён в файл: {args.output}")
        print("="*70)
        
    except KeyboardInterrupt:
        logger.info("Обход прерван пользователем")
        if parser.formulas:
            # Сохраняем то, что успели собрать
            output_name = args.output.replace('.json', '_partial.json')
            parser.save_formulas_to_json(output_name)
            print(f"Частичные результаты сохранены в {output_name}")
        
    except Exception as e:
        logger.error(f"Критическая ошибка: {e}")
        if parser.formulas:
            # Сохраняем результаты в резервную копию
            output_name = args.output.replace('.json', '_backup.json')
            parser.save_formulas_to_json(output_name)
            print(f"Резервная копия сохранена в {output_name}")

if __name__ == "__main__":
    main()