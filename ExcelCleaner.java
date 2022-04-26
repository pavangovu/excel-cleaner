import java.io.*;
import org.apache.poi.ss.usermodel.*;
import com.monitorjbl.xlsx.StreamingReader;
import com.monitorjbl.xlsx.impl.StreamingWorkbook;

public class ExcelCleaner {

	public static boolean clean(String input) {
		try {
			InputStream is = new FileInputStream(new File(input));
			Workbook workbook = StreamingReader.builder().rowCacheSize(100) // number of rows to keep in memory
																			// (defaults to 10)
					.bufferSize(4096) // buffer size to use when reading InputStream to file (defaults to 1024)
					.open(is); // InputStream or File for XLSX file (required)

			PrintWriter text;
			for (Sheet sheet : workbook) {
				text = new PrintWriter("./" + sheet.getSheetName() + ".txt");
				int rowCount = 0;
				int colCount = 0;
				String sheetName = sheet.getSheetName();
				
				for (Row r : sheet) {
					
					rowCount++; //increment number of rows detected
					
					if (isRowEmpty(r)){
						rowCount--;
						continue; //skip processing of this row
					}
					
					//number of columns detected by the system
					if (rowCount==1)
					colCount=r.getLastCellNum();//number of expected columns = number of headers
					
					for (Cell c : r) {
						System.out.print(c.getStringCellValue());
						if(c.getStringCellValue().equals("ConfigurationType"))
							System.out.print("");
						//text.write(c.getStringCellValue());
						System.out.print("\t");
						//text.write("\t");
					}
					System.out.println();
					//text.write("\n");	
				}
				
				text.write("Row count after cleaning: "+rowCount);
				text.write("\n");
				text.write("Column count after cleaning: ");
				text.write("\n");
				text.write("Sheet name: "+sheetName);
				text.write("\n");
				text.close();
			}
		}

		catch (Exception error) {
			System.out.println("ERROR\n\n");
			System.out.println(error.toString());
			System.out.println("ERROR\n\n");
			return false;
		}

		return false; // preserve false for now
	}

	// checks if a given row is empty
	public static boolean isRowEmpty(Row row) {
		boolean isEmpty = true;
		DataFormatter dataFormatter = new DataFormatter();

		if (row != null) {
			for (Cell cell : row) {
				if (!cell.getStringCellValue().isEmpty()) {
					isEmpty = false;
					break;
				}
			}
		}

		return isEmpty; // return the result
	}

	// main used for local testing purposes only
	public static void main(String[] args) {
		String inputFile = "C:\\Users\\egovpav\\OneDrive - Ericsson\\Ericsson\\WashingtonDCXMLIssue\\InputCIQ\\ISF117033_LTE_RND_T-Mobile_RND_CIQ_MMBB_02142022.xlsx";
		System.out.println(clean(inputFile));
	}
}