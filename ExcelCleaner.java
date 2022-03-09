package com.ericsson.utran.tools.intern;

import org.apache.poi.ss.usermodel.*;
import org.apache.poi.xssf.usermodel.*;
import java.io.*;
import java.util.*;

public class ExcelCleaner {

	public static void main(String[] args) {
		List<String[]> cellValues = extractInfo(new File("C:\\workspace2\\Tools\\src\\com\\ericsson\\utran\\tools\\intern\\info.xlsx"));

		cellValues.forEach(c -> System.out.println(c[0] + ", " + c[1] + ", " + c[2] + ", " + c[3] + ", " + c[4]));

		try {
			writeToExcel(cellValues, new File("C:\\workspace2\\Tools\\src\\com\\ericsson\\utran\\tools\\intern\\deleted_empty_rows_info.xlsx"));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		System.out.println("Done!");
	}
	
	private static List<String[]> extractInfo(File file)
	{
		// TODO Auto-generated method stub
		Workbook book = null;
		
		List<String[]> infoList = new ArrayList<String[]>();
		
		try
		{
			book = new XSSFWorkbook(new FileInputStream(file));
			Sheet sheet = book.getSheetAt(0);
			
			for(Row row: sheet)
			{
				if(isRowEmpty(row))
				{
					continue;
				}
				
				List<Cell> cells = new ArrayList<Cell>();
				
				int lastColumn=Math.max(row.getLastCellNum(), 5);
				
				for(int columnNumber = 0; columnNumber < lastColumn; columnNumber++)
				{
					Cell currentCell = row.getCell(columnNumber, Row.MissingCellPolicy.RETURN_BLANK_AS_NULL);
					cells.add(currentCell);
				}
				
				String[] cellValues = extractInfoFromCell(cells);
				infoList.add(cellValues);
			}
		} 
		
		catch(IOException e)
		{
			e.printStackTrace();
		} 
		
		finally
		{
			if(book!=null)
			{
				try
				{
					book.close();
				}
				catch(IOException e)
				{
					e.printStackTrace();
				}
			}
		}
		
		return infoList;
	}

	private static String[] extractInfoFromCell(List<Cell> cells) {
		String[] cellValues = new String[5];

		cellValues[0] = getCellValue(cells.get(0));

		cellValues[1] = getCellValue(cells.get(1));

		cellValues[2] = getCellValue(cells.get(2));

		cellValues[3] = getCellValue(cells.get(3));

		cellValues[4] = getCellValue(cells.get(4));

		return cellValues;
	}

	private static String getCellValue(Cell cell) {
		String val = "";

		switch (cell.getCellType()) {
		case Cell.CELL_TYPE_NUMERIC:
			val = String.valueOf(cell.getNumericCellValue());
			break;
		case Cell.CELL_TYPE_STRING:
			val = cell.getStringCellValue();
			break;
		case Cell.CELL_TYPE_BLANK:
			break;
		case Cell.CELL_TYPE_BOOLEAN:
			val = String.valueOf(cell.getBooleanCellValue());
			break;
		case Cell.CELL_TYPE_ERROR:
			break;
		case Cell.CELL_TYPE_FORMULA:
			break;
		default:
			break;
		}

		return val;
	}

	private static boolean isRowEmpty(Row row) {
		boolean isEmpty = true;
		DataFormatter dataFormatter = new DataFormatter();

		if (row != null) {
			for (Cell cell : row) {
				if (dataFormatter.formatCellValue(cell).trim().length() > 0) {
					isEmpty = false;
					break;
				}
			}
		}

		return isEmpty;
	}
	
	public static void writeToExcel(List<String[]> cellValues, File outputFile) throws IOException {
		Workbook wb = new XSSFWorkbook();

		OutputStream outputStream = new FileOutputStream(outputFile);

		Sheet sheet = wb.createSheet();

		int rows = cellValues.size();
		int cells = cellValues.get(0).length;

		for (int i = 0; i < rows; i++) {
			Row row = sheet.createRow(i);

			for (int j = 0; j < cells; j++) {
				Cell cell = row.createCell(j);
				cell.setCellValue(cellValues.get(i)[j]);
			}
		}

		wb.write(outputStream);
		wb.close();
	}

}
