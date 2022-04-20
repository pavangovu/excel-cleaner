package com.ericsson.utran.tools.intern;

import java.io.*;
import java.util.*;

import org.apache.poi.ss.usermodel.*;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

public class ExcelCleaner {

	public static boolean clean(String input)
	{
		
		return false;
	}
	
    public static void main(String[] args) {

        //Create an ArrayList to store the data read from excel file
        ArrayList<ArrayList<Object>> data = new ArrayList<>();

        try {
            //Create an FileInputStream to read the xlsx file
            FileInputStream fis = new FileInputStream(new File("C:\\workspace2\\Tools\\src\\com\\ericsson\\utran\\tools\\intern\\info.xlsx"));

            //Create an XSSFWorkbook object for our file system
            XSSFWorkbook workbook = new XSSFWorkbook(fis);

            //Get the number of sheets in the xlsx file
            int numberOfSheets = workbook.getNumberOfSheets();

            //loop through each of the sheets
            for(int i=0; i < numberOfSheets; i++){

                //Get the nth sheet from the workbook
                Sheet sheet = workbook.getSheetAt(i);

                //every sheet has rows, iterate over them
                Iterator<Row> rowIterator = sheet.iterator();
                while (rowIterator.hasNext())
                {
                    //Get the row object
                    Row row = rowIterator.next();

                    //Every row has columns, get the column iterator and iterate over them
                    Iterator<Cell> cellIterator = row.cellIterator();

                    ArrayList<Object> rowData = new ArrayList<>();

                    //Fetch each cell in a row
                    while (cellIterator.hasNext())
                    {
                        //Get the Cell object
                        Cell cell = cellIterator.next();

                        //check the cell type and process accordingly
                        switch(cell.getCellType())
                        {
                            case Cell.CELL_TYPE_NUMERIC:
                                rowData.add(cell.getNumericCellValue());
                                break;
                            case Cell.CELL_TYPE_STRING:
                                rowData.add(cell.getStringCellValue());
                                break;
                            case Cell.CELL_TYPE_BOOLEAN:
                                rowData.add(cell.getBooleanCellValue());
                                break;
                            case Cell.CELL_TYPE_FORMULA:
                                rowData.add(cell.getCellFormula());
                                break;
                            default:
                                break;
                        }
                    }

                    //add the rowData to the data
                    data.add(rowData);
                    System.out.println("Add row line 72");
                }
            }

            fis.close();

            //Remove empty rows
            data.removeAll(Collections.singleton(null));

            //Remove empty columns
            for (ArrayList<Object> rowData: data) {
                rowData.removeAll(Collections.singleton(null));
            }

            //Print the data read from excel file
            System.out.println(data);

        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}