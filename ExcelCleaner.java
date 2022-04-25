package com.ericsson.utran.tools.intern;

import java.io.*;
import org.apache.poi.ss.usermodel.*;
import com.monitorjbl.xlsx.StreamingReader;

public class ExcelCleaner {

	public static boolean clean(String input)
	{
		try
		{
			InputStream is = new FileInputStream(new File(input));
			Workbook workbook = StreamingReader.builder()
			        .rowCacheSize(100)    // number of rows to keep in memory (defaults to 10)
			        .bufferSize(4096)     // buffer size to use when reading InputStream to file (defaults to 1024)
			        .open(is);            // InputStream or File for XLSX file (required)
			
			for (Sheet sheet : workbook){
				  System.out.println(sheet.getSheetName());
				  for (Row r : sheet) {
				    for (Cell c : r) {
				      System.out.println(c.getStringCellValue());
				    }
				  }
				}
		}
		
		catch (Exception error)
		{
			System.out.println(error.getMessage());
			return false;
		}
                    
		return false; //preserve false for now
	}
	
	//main used for local testing purposes only
    public static void main(String[] args) 
    {
    	String inputFile = "C:\\Users\\egovpav\\OneDrive - Ericsson\\Ericsson\\WashingtonDCXMLIssue\\InputCIQ\\ISF117033_LTE_RND_T-Mobile_RND_CIQ_MMBB_02142022.xlsx";
    	System.out.println(clean(inputFile));
    }
}