package com.ericsson.utran.tools.intern;

import org.apache.poi.ss.usermodel.*;
import org.apache.poi.xssf.usermodel.*;
import java.io.*;
import java.util.*;
import java.util.Map.Entry;

public class ExcelCleaner {

	public static void main(String[] args) {
		System.out.println("Start!");
		
		//List<String[]> cellValues = extractInfo(new File("C:\\workspace2\\Tools\\src\\com\\ericsson\\utran\\tools\\intern\\info.xlsx"));

		Map<String, List<List<Cell>>> complete_Raw = extractInfo_Raw(new File("C:\\workspace2\\Tools\\src\\com\\ericsson\\utran\\tools\\intern\\info.xlsx"));
		//List<List<List<Cell>>> complete_Raw = extractInfo_Raw(new File("C:\\workspace2\\Tools\\src\\com\\ericsson\\utran\\tools\\intern\\info.xlsx"));
		
		//Print Cell Data to Console
		//cellValues.forEach(c -> System.out.println(c[0] + ", " + c[1] + ", " + c[2] + ", " + c[3] + ", " + c[4]));
		
		//perform datachecks
		/*System.out.println("Beginning data validation...");
		System.out.println("Number of sheets: "+complete_Raw.size());
		for(int i=0; i<complete_Raw.size(); i++)
		{
			System.out.println("Number of rows in sheet#"+(i+1)+": "+complete_Raw.get(i).size());
		}*/
		
		
		try {
			writeToExcel_Raw(complete_Raw, new File("C:\\workspace2\\Tools\\src\\com\\ericsson\\utran\\tools\\intern\\deleted_empty_rows_info.xlsx"));
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			//System.out.println("Errorthrown!!!!");
		}
		
		System.out.println("Done!");
	}

	private static Map<String, List<List<Cell>>> extractInfo_Raw(File file)
	{
		// TODO Auto-generated method stub
		Workbook book = null;
		Map<String, List<List<Cell>>> complete = new LinkedHashMap<>();	
		
		try
		{
			book = new XSSFWorkbook(new FileInputStream(file));
			
			int sheetCount=book.getNumberOfSheets();
			
			for(int currSheet=0; currSheet<sheetCount; currSheet++)
			{
				//System.out.print("here");
				Sheet sheet = book.getSheetAt(currSheet);
				String sheetName = sheet.getSheetName();
				
				List<List<Cell>> infoList_Raw = new ArrayList<>();
				
				int rowCount=1;
				for(Row row: sheet)
				{
					//System.out.println("Reading row #"+rowCount++);
					rowCount++;
					//leave behind empty rows
					if(isRowEmpty(row))
					{
						//System.out.println("Skipping empty row^^");
						rowCount--;
						continue;
					}
					
					List<Cell> cells = new ArrayList<Cell>();
					
					//reads in number of columns
					int lastColumn=row.getLastCellNum();
					//System.out.println("Columns detected: "+ lastColumn);
					
					for(int columnNumber = 0; columnNumber < lastColumn; columnNumber++)
					{
						Cell currentCell = row.getCell(columnNumber, Row.MissingCellPolicy.RETURN_BLANK_AS_NULL);						
						
						if(!(currentCell==null))
						cells.add(currentCell);
					}

					List<Cell> cellValues_Raw = extractInfoFromCell_Raw(cells);
					infoList_Raw.add(cellValues_Raw);
				}
				System.out.println("Rows identified in sheet#"+(currSheet+1)+": "+infoList_Raw.size());
				complete.put(sheetName, infoList_Raw);
				System.out.println("Current sheet count: "+complete.size());
			}
		} 
		
		catch(IOException e)
		{
			e.printStackTrace();
			System.out.println(e.getMessage());
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
		
		return complete;
	}
	
	private static List<Cell> extractInfoFromCell_Raw(List<Cell> cells) {

		List<Cell> cellValues = new ArrayList<>();
		
		for(int i=0; i<cells.size(); i++)
		{
			cellValues.add(getCellValue_Raw(cells.get(i)));
		}

		return cellValues;
	}
	
	private static Cell getCellValue_Raw(Cell cell) {
		Cell val = null;

		//System.out.println("Cell");
		
		switch (cell.getCellType()) {
		case Cell.CELL_TYPE_NUMERIC:
			val = cell;
			break;
		case Cell.CELL_TYPE_STRING:
			val = cell;
			break;
		case Cell.CELL_TYPE_BLANK:
			break;
		case Cell.CELL_TYPE_BOOLEAN:
			val = cell;
			break;
		case Cell.CELL_TYPE_ERROR:
			break;
		case Cell.CELL_TYPE_FORMULA:
			val=cell;
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
	
	public static void writeToExcel_Raw(Map<String, List<List<Cell>>> completeValues, File outputFile) throws IOException {
		Workbook wb = new XSSFWorkbook();

		OutputStream outputStream = new FileOutputStream(outputFile);

		for(Entry<String, List<List<Cell>>> currentSheet: completeValues.entrySet())
		{
			Sheet sheet = wb.createSheet(currentSheet.getKey());
			List<List<Cell>> cellValues = currentSheet.getValue();
			
			//traverse rows
			for (int i = 0; i < cellValues.size(); i++) 
			{
				Row row = sheet.createRow(i);
				System.out.print("Row #"+(i+1)+": ");

				//traverse columns for that particular row
				for (int j = 0; j < cellValues.get(i).size(); j++) 
				{
					Cell cell = row.createCell(j);
					Cell rawCell=cellValues.get(i).get(j);
					
					cell.setCellType(rawCell.getCellType());
					
					switch (rawCell.getCellType()) {
					case Cell.CELL_TYPE_NUMERIC:
						cell.setCellValue(Math.round(rawCell.getNumericCellValue()));
						break;
					case Cell.CELL_TYPE_STRING:
						cell.setCellValue(rawCell.getStringCellValue());
						break;
					case Cell.CELL_TYPE_BOOLEAN:
						cell.setCellValue(rawCell.getBooleanCellValue());
						break;
					case Cell.CELL_TYPE_FORMULA:
						cell.setCellValue(rawCell.getCellFormula());
						break;
					default:
						cell.setCellValue("phineas");
						break;
					}
					System.out.print(cell.toString()+", ");//print values in current row
				}
				
				//newline for next row
				System.out.println();
			}
		}

		wb.write(outputStream);
		wb.close();
	}
}
