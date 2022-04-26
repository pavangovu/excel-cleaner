package com.ericsson.utran.tools.shared;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.PrintStream;
import java.io.Reader;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

import org.apache.poi.hssf.usermodel.HSSFSheet;
import org.apache.poi.hssf.usermodel.HSSFWorkbook;
import org.apache.poi.openxml4j.opc.OPCPackage;
import org.apache.poi.openxml4j.opc.PackageAccess;
import org.apache.poi.ss.usermodel.Cell;
import org.apache.poi.ss.usermodel.DataFormatter;
import org.apache.poi.ss.usermodel.Row;
import org.apache.poi.ss.usermodel.Sheet;
import org.apache.poi.ss.usermodel.Workbook;
import org.apache.poi.ss.usermodel.WorkbookFactory;
import org.apache.poi.xssf.usermodel.XSSFSheet;
import org.apache.poi.xssf.usermodel.XSSFWorkbook;

import com.ericsson.utran.tools.GlobalConst;
import com.ericsson.utran.tools.intern.ExcelCleaner;
import com.ericsson.utran.tools.tmo_ericsson.TMOConstants;
import com.opencsv.CSVParser;
import com.opencsv.CSVParserBuilder;
import com.opencsv.CSVReader;
import com.opencsv.CSVReaderBuilder;
import com.opencsv.CSVWriter;

/**
 * Class with custom methods for CU agnostic handling of CSV files
 */
public class CSVUtils
{
	private static final org.apache.logging.log4j.Logger logger = org.apache.logging.log4j.LogManager.getLogger(CSVUtils.class);
	private static Logger gmoLogger = Logger.getGmoLogger();

	private ArrayList<String> sheetsToProcess;
	private File rndCiqFile;
	private HashMap<String, File> ciqs;
	private static HashMap<String, File> mocToKgetCsvFile = new HashMap<String, File>();
	private static Map<String, String> mocParamToDefaultValue;
	private String cu;
	public File caDynRnCSV;
	public File caENodeBCSV;
	public File caRachRootSequenceCSV;
	public File mktDataCSV;
	public File radioPIUTypeCSV;
	public File tmoOssListCSV;

	/*** [euttsaw] 3/15/18: Update to execute convertCIQToCSV::excel2CSV() for T-Mobile XLSX/XLS CIQs using tmoSheetPresent until POI is updated to 
	 * detect hidden sheets for XLSX CIQs ***/
	private static boolean tmoSheetPresent = false;

	private static boolean isTestServer = ServerInfo.isTestServer();

	/**
	 * key: name of CSV file minus file extension (example: CMCIQ_FEATUREMAP, ATND_ATND)
	 * value: CSV File
	 */
	private static Map<String, File> ciqCSVs = new HashMap<String, File>();

	public static File getCIQCSVFile(String fileName)
	{
		File ciqCSVFile = null;
		try {
			if (ciqCSVs.containsKey(fileName)) {
				ciqCSVFile = ciqCSVs.get(fileName);
			}
			else {
				File csvFile = new File(FileUtil.getCmCiqDirectory() + File.separator + fileName + ".csv");
				if (csvFile.exists()) {
					ciqCSVFile = csvFile;
				}
			}
		}
		catch (Exception e) {
			logger.error("getCIQCSVFile exception!", e);
			gmoLogger.printError("Get CIQ CSV file exception! " + e.getMessage());
		}
		return ciqCSVFile;
	}


	public static void setCIQCSVFile(String fileNameKey, File file)
	{
		try {
			if (ciqCSVs.containsKey(fileNameKey)) {
				if (file != null && file.exists() && !file.equals(ciqCSVs.get(fileNameKey))) {
					Logger.getGmoLogger().printWarning("Updating reference for " + fileNameKey);
				}
			}
			ciqCSVs.put(fileNameKey, file);
		}
		catch (Exception e) {
			Logger.logger.error("setCIQCSVFile exception!", e);
			Logger.getGmoLogger().printError("Error setting CIQ CSV map! " + e.getMessage());
		}
	}

	/**
	 * default constructor
	 */
	public CSVUtils()
	{
	}

	/**
	 * Constructor to initialize CIQs
	 * @param ciqs - RND, CACIQ, RF, ATND, KGET, MKTDATA, CMCIQ
	 * @param rndSheetsToProcess - sheets in RND to process
	 * @param mocList - MOC list for KGET processing
	 * @param cu - customer filter
	 */
	public CSVUtils(HashMap<String, File> ciqs, ArrayList<String> rndSheetsToProcess, List<String> mocList, String cu)
	{
		this.ciqs = ciqs;
		this.cu = cu;
		if (rndSheetsToProcess != null) {
			sheetsToProcess = rndSheetsToProcess;
			/*** [euttsaw] 3/15/18: Update to execute convertCIQToCSV::excel2CSV() for T-Mobile XLSX/XLS CIQs using tmoSheetPresent until POI is updated to 
			 * detect hidden sheets for XLSX CIQs ***/
			if (sheetsToProcess.contains("LTE-GSM-FreqGroupRel") || sheetsToProcess.contains("GSM Nbr Cell")) {
				if (cu.equalsIgnoreCase("Rogers")) {
					// do nothing
				}
				else {
					tmoSheetPresent = true;
				}
			}
		}
		else {
			sheetsToProcess = new ArrayList<String>();
		}

		if (ciqs.containsKey("RND")) {
			initializeRND();
		}
		// if (ciqs.containsKey("WCDMA")) { // eusxjas
		// initializeWcdmaRND();
		// }
		if (!cu.equalsIgnoreCase("TMO") && ciqs.containsKey("KGET")) {
			initializeKGET(mocList);
		}
		if (ciqs.containsKey("GSM")) {
			if(cu.equalsIgnoreCase("TMO"))
				initializeGSMData();
			else
				initializeKGET(mocList);
		}
		if (ciqs.containsKey("CACIQ")) {
			initializeCACIQ();
		}
		if (ciqs.containsKey("CMCIQ")) {
			convertCIQToCSV(ciqs.get("CMCIQ"), "FeatureMap", "CMCIQ_FEATUREMAP");
			convertCIQToCSV(ciqs.get("CMCIQ"), "RiLink_Numbering", "CMCIQ_RILINKNUMBERING");
			convertCIQToCSV(ciqs.get("CMCIQ"), "Sw_repertoires", "CMCIQ_SWREPERTOIRES");
			convertCIQToCSV(ciqs.get("CMCIQ"), "DUS_supportsystemcontrol", "CMCIQ_DUSSUPPORTSYSTEMCONTROL");
			convertCIQToCSV(ciqs.get("CMCIQ"), "Configuration_to_RET_Unique_Id", "CMCIQ_CONFIGURATIONTORETUNIQUEID");
			convertCIQToCSV(ciqs.get("CMCIQ"), "RET_Delete", "CMCIQ_RETDELETE");
			convertCIQToCSV(ciqs.get("CMCIQ"), "RET_Configuration", "CMCIQ_RETCONFIGURATION");
			convertCIQToCSV(ciqs.get("CMCIQ"), "Determine_Start_Config", "CMCIQ_DETERMINESTARTCONFIG");
			convertCIQToCSV(ciqs.get("CMCIQ"), "Two_Night_Approach", "CMCIQ_TWONIGHTAPPROACH");
			convertCIQToCSV(ciqs.get("CMCIQ"), "MultiDu_WCDMA_ExternalNode", "CMCIQ_MULTIDUWCDMAEXTERNALNODE");
			convertCIQToCSV(ciqs.get("CMCIQ"), "WCDMA_MixedMode", "CMCIQ_WCDMAMIXEDMODE");
			convertCIQToCSV(ciqs.get("CMCIQ"), "Config_Specific_RiLink_Settings", "CMCIQ_CONFIGSPECIFICRILINKSETTINGS");
			convertCIQToCSV(ciqs.get("CMCIQ"), "MultiDu_Parameter_Update", "CMCIQ_MULTIDUPARAMETERUPDATE");
			convertCIQToCSV(ciqs.get("CMCIQ"), "MultiDu_RiPort_Table", "CMCIQ_MULTIDURIPORTTABLE");
			convertCIQToCSV(ciqs.get("CMCIQ"), "MultiDu_RBB_RFB_RFP_Table", "CMCIQ_MULTIDURBBRFBRFPTABLE");
			convertCIQToCSV(ciqs.get("CMCIQ"), "MultiDu_RBB_Table", "CMCIQ_MULTIDURBBTABLE");
			convertCIQToCSV(ciqs.get("CMCIQ"), "BB5216_Config_to_Use_Case", "CMCIQ_BB5216CONFIGTOUSECASE");
			convertCIQToCSV(ciqs.get("CMCIQ"), "BB6630_Config_to_Use_Case", "CMCIQ_BB6630CONFIGTOUSECASE");
			convertCIQToCSV(ciqs.get("CMCIQ"), "Asymmetric_Configs_List", "CMCIQ_ASYMMETRICCONFIGSLIST");
			convertCIQToCSV(ciqs.get("CMCIQ"), "CellBandToCellBandString", "CMCIQ_CELLBANDTOCELLBANDSTRING");
			convertCIQToCSV(ciqs.get("CMCIQ"), "Scope_To_Script_Technology_Map", "CMCIQ_SCOPETOSCRIPTTECHNOLOGYMAP");
			convertCIQToCSV(ciqs.get("CMCIQ"), "WCDMA_RBB_Types", "CMCIQ_WCDMARBBTYPES");
			convertCIQToCSV(ciqs.get("CMCIQ"), "HW", "CMCIQ_HW");
			convertCIQToCSV(ciqs.get("CMCIQ"), "RBB", "CMCIQ_RBB");
			convertCIQToCSV(ciqs.get("CMCIQ"), "MME", "MME");
			convertCIQToCSV(ciqs.get("CMCIQ"), "SW_Lvl_Map", "CMCIQ_SWLVLMAP");
			convertCIQToCSV(ciqs.get("CMCIQ"), "Submarket_ENM_Map", "CMCIQ_SUBMARKETENMMAP");
			convertCIQToCSV(ciqs.get("CMCIQ"), "SubNetwork_Market_Map", "CMCIQ_SUBNETWORKMARKETMAP");
		}
		if (ciqs.containsKey("PIUTYPE")) {
			radioPIUTypeCSV = convertCIQToCSV(ciqs.get("PIUTYPE"), "RADIO_PIUTYPE", "RADIO_PIUTYPE");
		}

		if (ciqs.containsKey("EDP")) {
			convertCIQToCSV(ciqs.get("EDP"), "raptor", "EDP_raptor");
		}

		if (ciqs.containsKey("MKTDATA")) {
			mktDataCSV = convertCIQToCSV(ciqs.get("MKTDATA"), "MARKET_DATA_SHEET", "MKTDATA_MARKETDATASHEET");
			ciqCSVs.put("MKTDATA_MARKETDATASHEET", convertCIQToCSV(ciqs.get("MKTDATA"), "MARKET_DATA_SHEET", "MKTDATA_MARKETDATASHEET"));
			ciqCSVs.put("MKTDATA_MME", convertCIQToCSV(ciqs.get("MKTDATA"), "MME", "MKTDATA_MME"));
			ciqCSVs.put("MKTDATA_GREENFIELD", convertCIQToCSV(ciqs.get("MKTDATA"), "Greenfield", "MKTDATA_GREENFIELD"));
			ciqCSVs.put("MKTDATA_AP", convertCIQToCSV(ciqs.get("MKTDATA"), "AP", "MKTDATA_AP"));
			ciqCSVs.put("MKTDATA_TMO_OSS", convertCIQToCSV(ciqs.get("MKTDATA"), "TMO_OSS", "MKTDATA_TMO_OSS"));
			ciqCSVs.put("MKTDATA_TMO_BSIM_TEMPLATE", convertCIQToCSV(ciqs.get("MKTDATA"), "TMO_BSIM_TEMPLATE", "MKTDATA_TMO_BSIM_TEMPLATE"));
			convertCIQToCSV(ciqs.get("MKTDATA"), "ATT National NSB Only", "MKTDATA_ATTNATLNSBONLY");
			convertCIQToCSV(ciqs.get("MKTDATA"), "ATT Market Indicators", "MKTDATA_ATTMKTINDICATORS");
		}
		if (ciqs.containsKey("TMOOSSLIST")) {
			tmoOssListCSV = convertCIQToCSV(ciqs.get("TMOOSSLIST"), "TMOoss", "TMOoss");
			ciqCSVs.put("TMOoss", tmoOssListCSV);
		}
		if (ciqs.containsKey("ATND")) {
			if (ciqs.get("ATND").getName().toLowerCase().matches(".+\\.xlsx?$")) {
				ciqCSVs.put("ATND_ATND", convertCIQToCSV(ciqs.get("ATND"), "ATND", "ATND_ATND"));
				ciqCSVs.put("ATND_ENODEB", convertCIQToCSV(ciqs.get("ATND"), "eNodeB", "ATND_ENODEB"));
				ciqCSVs.put("ATND_SHEET1", convertCIQToCSV(ciqs.get("ATND"), "Sheet1", "ATND_SHEET1"));
				ciqCSVs.put("ATND_BEARER", convertCIQToCSV(ciqs.get("ATND"), "Bearer MMBTS-SPx10 4G", "ATND_BEARER"));

				ciqCSVs.put("ATND_GNODEB", convertCIQToCSV(ciqs.get("ATND"), "gNodeB Ericsson", "ATND_GNODEB"));
				ciqCSVs.put("ATND_ENODEB_ERICSSON", convertCIQToCSV(ciqs.get("ATND"), "eNodeB Ericsson", "ATND_ENODEB_ERICSSON"));
			}
			else if (ciqs.get("ATND").getName().toLowerCase().matches(".+\\.csv$")) {
				ciqCSVs.put("ATND_ATND", ciqs.get("ATND"));
			}
		}
		if (ciqs.containsKey("LTEATNDDATAFILL")) {
			if (ciqs.get("LTEATNDDATAFILL").getName().toLowerCase().matches(".+\\.xlsx?$")) {
				ciqCSVs.put("LTEATNDDATAFILL", convertCIQToCSV(ciqs.get("LTEATNDDATAFILL"), "Datafill", "LteDatafill"));
			}
		}
		if (ciqs.containsKey("UMTSATNDDATAFILL")) {
			if (ciqs.get("UMTSATNDDATAFILL").getName().toLowerCase().matches(".+\\.xlsx?$")) {
				ciqCSVs.put("UMTSATNDDATAFILL", convertCIQToCSV(ciqs.get("UMTSATNDDATAFILL"), "Datafill", "UmtsDatafill"));
			}
		}
	}

	/**
	 * Constructor to initialize WCDMA RND CIQs
	 * @param ciqs - WCDMA, RND
	 */
	// eusxjas 06/27/2018
	public CSVUtils(HashMap<String, File> ciqs, ArrayList<String> wcdmaRndSheetsToProcess, Boolean wcdmaPresent)
	{
		if (wcdmaPresent) {
			this.ciqs = ciqs;
			if (wcdmaRndSheetsToProcess != null) {
				sheetsToProcess = wcdmaRndSheetsToProcess;
			}
			else {
				sheetsToProcess = new ArrayList<String>();
			}

			if (ciqs.containsKey("WCDMA")) {
				initializeWcdmaRND();
			}
		}
	}

	/**
	 * Constructor to initialize rndCiqFile, kgetExtractFile, caCiqFile, cmCiqFile
	 * @param rndCiqFile
	 * @param kgetExtractFile
	 * @param caCiqFile
	 * @param cmCiqFile
	 */
	public CSVUtils(File rndCiqFile, File kgetExtractFile, File caCiqFile, File cmCiqFile)
	{
		if (rndCiqFile != null && rndCiqFile.exists()) {
			this.rndCiqFile = rndCiqFile;
			convertRNDToCSV(rndCiqFile, sheetsToProcess);
		}
		if (kgetExtractFile != null && kgetExtractFile.exists()) {
			populateMOCToKgetCsvFile(kgetExtractFile, CiqConstants.mocListForCSVLogic);
		}
		if (caCiqFile != null && caCiqFile.exists()) {
			caENodeBCSV = convertCIQToCSV(caCiqFile, "eNodeB", "CACIQ_ENODEB");
			caDynRnCSV = convertCIQToCSV(caCiqFile, "dyn RN", "CACIQ_DYNRN");
			caRachRootSequenceCSV = convertCIQToCSV(caCiqFile, "rachrootsequence", "CACIQ_RACHROOTSEQUENCE");
		}
		if (cmCiqFile != null && cmCiqFile.exists()) {
			convertCIQToCSV(cmCiqFile, "FeatureMap", "CMCIQ_FEATUREMAP");
			convertCIQToCSV(cmCiqFile, "RiLink_Numbering", "CMCIQ_RILINKNUMBERING");
		}
	}

	/**
	 * Constructor to initialize ericXmlHash
	 */
	public CSVUtils(HashMap<String, List<String>> ericXmlHash, String outDir, String fileName)
	{
		HashMap hmapColumn = new HashMap();
		HashMap<String, Integer> hmapColumnIndex = new HashMap<String, Integer>();

		try {
			/*** retrieve unique MOs ***/
			HashSet<String> uniqueMOs = new HashSet<String>();
			for (HashMap.Entry<String, List<String>> entry : ericXmlHash.entrySet()) {
				String mo = entry.getKey().split("!")[1];
				uniqueMOs.add(mo);
			}

			/*** initialize CSV files ***/
			for (String uniqueMO : uniqueMOs) {
				File csvFile = new File(outDir + File.separator + "Extracted_" + fileName + "_" + uniqueMO + ".csv");
				Files.deleteIfExists(csvFile.toPath());
				FileWriter fw = new FileWriter(csvFile.getPath());
				CSVWriter writer = new CSVWriter(fw);

				boolean headerExists = false;
				for (HashMap.Entry<String, List<String>> entry : ericXmlHash.entrySet()) {
					String mo = entry.getKey().split("!")[1];
					if (!mo.equals(uniqueMO)) {
						continue;
					}
					String site = entry.getKey().split("!")[0];
					String moId = entry.getKey().split("!")[2];
					String ldn = entry.getKey().split("!")[3];
					String esa = entry.getKey().split("!")[4];

					String[] paramValueArr = new String[entry.getValue().size()];
					paramValueArr = entry.getValue().toArray(paramValueArr);

					/*** header data ***/
					if (!headerExists) {
						/*** create record ***/
						ArrayList<String> record = new ArrayList<String>();

						record.add("Site");
						record.add(mo);
						record.add("LDN");
						record.add("ESA");
						for (String paramValue : paramValueArr) {
							record.add(paramValue.split("!")[0] + (Integer.parseInt(paramValue.split("!")[1]) > 0 ? paramValue.split("!")[1] : ""));
						}
						headerExists = true;

						/*** Write the record to file ***/
						if (record.size() > 0) {
							String[] newArray = new String[record.size()];
							writer.writeNext(record.toArray(newArray));
						}
					}

					/*** rest of data ***/
					/*** create record ***/
					ArrayList<String> record = new ArrayList<String>();

					record.add(site);
					record.add(moId);
					record.add(ldn);
					record.add(esa);
					for (String paramValue : paramValueArr) {
						record.add(paramValue.split("!").length > 2 ? paramValue.split("!")[2] : "");
					}
					headerExists = true;

					/*** Write the record to file ***/
					if (record.size() > 0) {
						String[] newArray = new String[record.size()];
						writer.writeNext(record.toArray(newArray));
					}
				}

				// close the writer
				writer.flushQuietly();
				writer.close();
				fw.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("CSVUtils exception! outDir=" + outDir + ", fileName=" + fileName, e);
			Logger.getGmoLogger().printError("Error constructing CSVUtils instance!");
		}

		hmapColumn.clear();
		hmapColumnIndex.clear();
	}

	/**
	 * Function to check if the required sheet exists in the ciqFile or not
	 * @param ciqFile
	 * @param sheetName
	 * @return
	 */
	public static boolean checkIfsheetExistsInExcel (File ciqFile, String sheetName) {
		boolean isSheetExists = false;
		try {
			if(!ciqFile.exists()) {
				return false;
			}
			Workbook workbook = WorkbookFactory.create(ciqFile, "", true);
			/*** Get first sheet from the workbook ***/
			Sheet sheet = null;
			for (int i = 0; i < workbook.getNumberOfSheets(); i++) {
				if (StringUtil.doesMatch(workbook.getSheetAt(i).getSheetName(), sheetName, Pattern.CASE_INSENSITIVE) && !(workbook.isSheetHidden(i) || workbook.isSheetVeryHidden(i))) {
					sheet = workbook.getSheetAt(i);
					break;
				}
			}
			if(sheet == null) {
				workbook.close();
				isSheetExists = false;
			}else {
				workbook.close();
				isSheetExists = true;
			}
			
		}catch(Exception e) {
			logger.error("checkIfsheetExistsInExcel exception" + e);
		}
		return isSheetExists;
	}

	/**
	 * Create a mapping between index of the column in a CSV file to the column name
	 * @param csvFile
	 * @return
	 */
	public static LinkedHashMap<Integer, String> columnIndexToHeaderMap(File csvFile)
	{
		LinkedHashMap<Integer, String> colNumToHeader = new LinkedHashMap<Integer, String>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);
				// Read all rows at once
				List<String[]> allRows = reader.readAll();
				
				/*** initialize column index ***/
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						/*** store header column index to map ***/
						if (!headerProcessed) {
							if (!row[j].isEmpty()) {
								colNumToHeader.put(j, row[j]);
							}
						}
					}
					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}
				}
				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("columnIndexToHeaderMap exception! csvFile=" + csvPath, e);
			Logger.getGmoLogger().printError("Error parsing headers from " + csvPath + "!");
		}
		return colNumToHeader;
	}

	/**
	 * reader - The reader to an underlying CSV source.
	 * line - The number of lines to skip before reading
	 */
	public static CSVReader constructCSVReader(Reader reader, int line)
	{
		CSVReader csvReader = null;
		try {
			CSVParser csvParser = new CSVParserBuilder().withSeparator(',').withQuoteChar('\"').withEscapeChar((char) 0).build();
			csvReader = new CSVReaderBuilder(reader).withCSVParser(csvParser).withSkipLines(line).build();
		}
		catch (Exception e) {
			logger.error("constructCSVReader exception!", e);
			gmoLogger.printError("Construct CSVReader exception! " + e.getMessage());
		}
		return csvReader;
	}
	
	/*
	 * [egovpav]
	 * [19 April 2022]
	 * 
	 * Remove excess columns and excess rows from .xlsx file
	 * 
	 * @param inputFile - input xlsx file
	 * @return result (if successful, path to cleaned file. Otherwise, return inputFile)
	 */
	
	public static String cleanExcel(String inputFile)
	{
		File input = new File(inputFile);
		String parentPath = input.getParent();
		String fileName = input.getName();
		
		boolean result = ExcelCleaner.clean(inputFile);
		
		if(result==true)
			return parentPath+"\\Cleaned\\"+fileName;	//path to cleaned file
		
		return inputFile;
	}

	/**
	 * Convert excel to CSV format.
	 * 
	 * @param ciqFile - Excel file
	 * @param sheetName - [regular expression] sheet to extract data from
	 * @param outputCSVFileName - output CSV file name
	 * @return CSV File
	 */
	public static File convertCIQToCSV(File ciqFile, String sheetName, String outputCSVFileName)
	{
		File csvFile = null;
		try {
			// if (GlobalConst.isGMODeveloper()) {
			/*** [euttsaw] 3/15/18: Update to execute excel2CSV for T-Mobile XLSX/XLS CIQs using tmoSheetPresent until POI is updated to 
			 * detect hidden sheets for XLSX CIQs ***/
			// [04082021 - eusxjas] If hidden sheets (supposedly not an issue recently), then engineer needs to manual adjust CIQ. Need to use XLSX conversion process to avoid memory usage issues for large RNDs, enables better success rate through S2G automation

			// TODO Other CUs still need to verify
			String fileExt = ".*\\.xlsx";
			if (GlobalConst.getProject() != null && GlobalConst.getProject().equalsIgnoreCase("T-Mobile")) {	// [05132021 - eusxjas]	Include only for TMO, including Excalibur parsing of Nokia CM data input
//				if ((SystemConstants.userSignum.toLowerCase().matches(SystemConstants.GMO_DEV_PROD) ||
//						SystemConstants.userSignum.toLowerCase().matches(SystemConstants.TMO_TESTERS) ||
//						(tmoSheetPresent || outputCSVFileName.startsWith("NOKIA_")))) {
					fileExt = ".*\\.xls[xm]";
//				}
			}
			if (StringUtil.doesMatch(ciqFile.getPath(), fileExt, Pattern.CASE_INSENSITIVE)) {	// [04022021] Trying this method for case of excessive large sheet in TMO
				//if (false) {
				PrintStream psTxt = null;
				OPCPackage p = null;
				csvFile = new File(FileUtil.getCmCiqDirectory() + File.separator + outputCSVFileName + ".csv");
				Files.deleteIfExists(csvFile.toPath());
				try {
					psTxt = new PrintStream(csvFile);
					p = OPCPackage.open(ciqFile.getPath(), PackageAccess.READ);
					XLSX2CSV xlsx2CSV = new XLSX2CSV(p, psTxt, -1, sheetName);
					xlsx2CSV.process();
				}
				catch (Exception e) {
					logger.error("Exception!", e);
					return null;
				}
				finally {
					if (psTxt != null) {
						psTxt.flush();
						psTxt.close();
					}
					if (p != null) {
						p.close();
					}
				}
			}
			else {
				csvFile = excel2CSV(ciqFile, sheetName, outputCSVFileName);
			}
		}
		catch (Exception e) {
			Logger.logger.error("convertCIQToCSV exception! ciqFile=" + ciqFile.getPath() + ", sheetName=" + sheetName + ", outputCSVFileName=" + outputCSVFileName, e);
			Logger.getGmoLogger().printError("Error converting " + ciqFile.getPath() + " \"" + sheetName + "\" to " + outputCSVFileName + "!");
		}
		return csvFile;
	}

	/**
	 * Convert CSV files to single EXCEL file. Each CSV file represents a sheet in the order inserted in the LinkedHashMap.
	 * 
	 * @param csvFileToSheetName - each entry represents 1 sheet of data
	 * @param outputExcelFile - output file name
	 * @return output File
	 */
	public static File convertCSVToExcel(LinkedHashMap<File, String> csvFileToSheetName, String outputExcelFile)
	{
		try {
			HSSFWorkbook workbook = new HSSFWorkbook();
			for (Map.Entry<File, String> entry : csvFileToSheetName.entrySet()) {
				File csvFile = entry.getKey();
				String sheetName = entry.getValue();

				logger.debug("Converting CSV sheet:" + sheetName + " to Excel");

				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);
				// Read all rows at once
				List<String[]> allRows = reader.readAll();
				HSSFSheet sheet = workbook.createSheet(sheetName);
				int rownum = 0;
				Cell cell = null;
				for (String[] csvRow : allRows) {
					Row row = sheet.createRow(rownum++);
					int cellnum = 0;
					for (int j = 0; j < csvRow.length; j++) {
						cell = row.createCell(cellnum++);
						cell.setCellValue(csvRow[j]);
					}
				}

				reader.close();
				fr.close();
			}

			File excelFile = new File(outputExcelFile);

			try {
				FileOutputStream out = new FileOutputStream(excelFile);
				workbook.write(out);
				out.close();
			}
			catch (Exception e) {
				String excelPath = excelFile != null ? excelFile.getPath() : "";
				Logger.logger.error("write exception! excelFile=" + excelPath, e);
				Logger.getGmoLogger().printError("Error writing to " + excelPath + "!");
			}

			workbook.close();
			return excelFile;
		}
		catch (Exception e) {
			Logger.logger.error("convertCSVToExcel exception! outputExcelFile=" + outputExcelFile, e);
			Logger.getGmoLogger().printError("Error converting CSVs to " + outputExcelFile + "!");
			return null;
		}
	}

	/**
	 * Convert CSV files to single EXCEL file. Each CSV file represents a sheet in the order inserted in the LinkedHashMap.
	 * 
	 * @param csvFileToSheetName - each entry represents 1 sheet of data
	 * @param outputExcelFile - output file name
	 * @return output File
	 */
	public static File convertCSVToExcelwithcellsize(LinkedHashMap<File, String> csvFileToSheetName, String outputExcelFile)
	{
		try {
			HSSFWorkbook workbook = new HSSFWorkbook();
			for (Map.Entry<File, String> entry : csvFileToSheetName.entrySet()) {
				File csvFile = entry.getKey();
				String sheetName = entry.getValue();

				logger.debug("Converting CSV sheet:" + sheetName + " to Excel");

				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);
				// Read all rows at once
				List<String[]> allRows = reader.readAll();
				HSSFSheet sheet = workbook.createSheet(sheetName);
				int rownum = 0;
				Cell cell = null;
				for (String[] csvRow : allRows) {
					Row row = sheet.createRow(rownum++);
					int cellnum = 0;
					for (int j = 0; j < csvRow.length; j++) {
						cell = row.createCell(cellnum++);
						if(!(csvRow[j].length()>=32767)) {
							cell.setCellValue(csvRow[j]);
						}
						
					}
				}

				reader.close();
				fr.close();
			}

			File excelFile = new File(outputExcelFile);

			if(!excelFile.exists()){
				excelFile.createNewFile();
				}
			
			try {
				FileOutputStream out = new FileOutputStream(excelFile);
				workbook.write(out);
				out.close();
			}
			catch (Exception e) {
				String excelPath = excelFile != null ? excelFile.getPath() : "";
				Logger.logger.error("write exception! excelFile=" + excelPath, e);
				Logger.getGmoLogger().printError("Error writing to " + excelPath + "!");
			}

			workbook.close();
			return excelFile;
		}
		catch (Exception e) {
			Logger.logger.error("convertCSVToExcel exception! outputExcelFile=" + outputExcelFile, e);
			Logger.getGmoLogger().printError("Error converting CSVs to " + outputExcelFile + "!");
			return null;
		}
	}

	/**
	 * Convert CSV files to single XLSX file. Each CSV file represents a sheet in the order inserted in the LinkedHashMap.
	 * 
	 * @param csvFileToSheetName - each entry represents 1 sheet of data
	 * @param outputExcelFile - output file name
	 * @return output File
	 */
	public static File convertCSVToXLSX(LinkedHashMap<File, String> csvFileToSheetName, String outputExcelFile)
	{
		try {
			XSSFWorkbook workbook = new XSSFWorkbook();
			for (Map.Entry<File, String> entry : csvFileToSheetName.entrySet()) {
				File csvFile = entry.getKey();
				String sheetName = entry.getValue();

				logger.debug("Converting CSV sheet:" + sheetName + " to Excel");

				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);
				// Read all rows at once
				List<String[]> allRows = reader.readAll();
				XSSFSheet sheet = workbook.createSheet(sheetName);
				int rownum = 0;
				Cell cell = null;
				for (String[] csvRow : allRows) {
					Row row = sheet.createRow(rownum++);
					int cellnum = 0;
					for (int j = 0; j < csvRow.length; j++) {
						cell = row.createCell(cellnum++);
						cell.setCellValue(csvRow[j]);
					}
				}

				reader.close();
				fr.close();
			}

			File excelFile = new File(outputExcelFile);

			try {
				FileOutputStream out = new FileOutputStream(excelFile);
				workbook.write(out);
				out.close();
			}
			catch (Exception e) {
				String excelPath = excelFile != null ? excelFile.getPath() : "";
				Logger.logger.error("write exception! excelFile=" + excelPath, e);
				Logger.getGmoLogger().printError("Error writing to " + excelPath + "!");
			}

			workbook.close();
			return excelFile;
		}
		catch (Exception e) {
			Logger.logger.error("convertCSVToXLSX exception! outputExcelFile=" + outputExcelFile, e);
			Logger.getGmoLogger().printError("Error converting CSVs to " + outputExcelFile + "!");
			return null;
		}
	}

	/**
	 * Convert Kget CSV files to single EXCEL file with multiple sheets.
	 * This is to handle scenarios where number of columns exceed limit of XLS.
	 * Each CSV file represents a sheet in the order inserted in the LinkedHashMap.
	 * 
	 * @param csvFileToSheetName - each entry represents 1 sheet of data
	 * @param outputExcelFile - output file name
	 * @return output File
	 */
	public static File convertKgetCsvToExcelWithMultipleSheets(LinkedHashMap<File, String> csvFileToSheetName, String outputExcelFile)
	{
		try {
			HSSFWorkbook workbook = new HSSFWorkbook();
			for (Map.Entry<File, String> entry : csvFileToSheetName.entrySet()) {
				File csvFile = entry.getKey();
				String sheetName = entry.getValue();
				String moc = sheetName.replaceAll("~$", "");

				logger.debug("Converting CSV sheet:" + moc + " to Excel");

				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);
				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				// calculate keys
				int indexNodeMOKey = 0;
				int indexMO = 0;
				int indexMocId = 0;
				for (int i = 0; i < allRows.get(0).length; i++) {
					if (allRows.get(0)[i].equals("NodeMOKey")) {
						indexNodeMOKey = i;
					}
					if (allRows.get(0)[i].equals("MO")) {
						indexMO = i;
					}
					if (allRows.get(0)[i].equalsIgnoreCase(moc + "Id")) {
						indexMocId = i;
					}
				}
				
				int columnLimit = 250;
				
				// calculate number of sheets
				int divValue = allRows.get(0).length / columnLimit;
				int modValue = allRows.get(0).length % columnLimit;
				int sheetCounter = divValue;
				if (modValue > 0) {
					sheetCounter++;
				}

				for (int i = 1; i <= sheetCounter; i++) {

					int startCell = (columnLimit * i) - columnLimit;
					int endCell = startCell + columnLimit;
//					if (allRows.get(0).length - startCell < columnLimit) {
//						endCell = startCell + startCell + allRows.get(0).length - (columnLimit * i);
//					}

					// update sheetName
					if (i > 1) {
						sheetName = sheetName.replaceAll("[\\d]*~$", i - 1 + "~");
					}

					HSSFSheet sheet = workbook.createSheet(sheetName);
					int rownum = 0;
					Cell cell = null;
					for (String[] csvRow : allRows) {
						Row row = sheet.createRow(rownum++);

						int createCellCounter = 0;
						for (int j = startCell; j < endCell; j++) {
							// exit when data runs out
							if (j >= csvRow.length) {
								break;
							}
							
							// create key columns for additional cellsheaders
							if (createCellCounter == 0) {
								cell = row.createCell(createCellCounter++);
								cell.setCellValue(csvRow[indexNodeMOKey]);
								cell = row.createCell(createCellCounter++);
								cell.setCellValue(csvRow[indexMO]);
								cell = row.createCell(createCellCounter++);
								cell.setCellValue(csvRow[indexMocId]);
							}

							// write all other column data (except for key columns)
							if (j != indexNodeMOKey && j != indexMO && j != indexMocId) {
								cell = row.createCell(createCellCounter++);
								cell.setCellValue(csvRow[j]);
							}
						}
					}
				}

				reader.close();
				fr.close();
			}

			File excelFile = new File(outputExcelFile);

			try {
				FileOutputStream out = new FileOutputStream(excelFile);
				workbook.write(out);
				out.close();
			}
			catch (Exception e) {
				String excelPath = excelFile != null ? excelFile.getPath() : "";
				Logger.logger.error("write exception! excelFile=" + excelPath, e);
				Logger.getGmoLogger().printError("Error writing to " + excelPath + "!");
			}

			workbook.close();
			return excelFile;
		}
		catch (Exception e) {
			Logger.logger.error("convertKgetCsvToExcelWithMultipleSheets exception! outputExcelFile=" + outputExcelFile, e);
			Logger.getGmoLogger().printError("Error converting KGET CSVs to " + outputExcelFile + "!");
			return null;
		}
	}

	
	/**
	 * Convert Kget CSV files to single EXCEL file with multiple sheets.
	 * This is to handle scenarios where number of columns exceed limit of XLS.
	 * Each CSV file represents a sheet in the order inserted in the LinkedHashMap.
	 * 
	 * @param csvFileToSheetName - each entry represents 1 sheet of data
	 * @param outputExcelFile - output file name
	 * @return output File
	 */
	public static File convertKgetCsvToExcelWithMultipleSheetswithlimitchange(LinkedHashMap<File, String> csvFileToSheetName, String outputExcelFile)
	{
		try {
			HSSFWorkbook workbook = new HSSFWorkbook();
			for (Map.Entry<File, String> entry : csvFileToSheetName.entrySet()) {
				File csvFile = entry.getKey();
				String sheetName = entry.getValue();
				String moc = sheetName.replaceAll("~$", "");

				logger.debug("Converting CSV sheet:" + moc + " to Excel");

				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);
				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				// calculate keys
				int indexNodeMOKey = 0;
				int indexMO = 0;
				int indexMocId = 0;
				for (int i = 0; i < allRows.get(0).length; i++) {
					if (allRows.get(0)[i].equals("NodeMOKey")) {
						indexNodeMOKey = i;
					}
					if (allRows.get(0)[i].equals("MO")) {
						indexMO = i;
					}
					if (allRows.get(0)[i].equalsIgnoreCase(moc + "Id")) {
						indexMocId = i;
					}
				}
				

				int columnLimit = ServerInfo.isTestServer()?251:251;
				
				// calculate number of sheets
				int divValue = allRows.get(0).length / columnLimit;
				int modValue = allRows.get(0).length % columnLimit;
				int sheetCounter = divValue;
				if (modValue > 0) {
					sheetCounter++;
				}

				for (int i = 1; i <= sheetCounter; i++) {

					int startCell = (columnLimit * i) - columnLimit;
					int endCell = startCell + columnLimit;
//					if (allRows.get(0).length - startCell < columnLimit) {
//						endCell = startCell + startCell + allRows.get(0).length - (columnLimit * i);
//					}

					// update sheetName
					if (i > 1) {
						sheetName = sheetName.replaceAll("[\\d]*~$", i - 1 + "~");
					}

					HSSFSheet sheet = workbook.createSheet(sheetName);
					int rownum = 0;
					Cell cell = null;
					for (String[] csvRow : allRows) {
						Row row = sheet.createRow(rownum++);

						int createCellCounter = 0;
						for (int j = startCell; j < endCell; j++) {
							// exit when data runs out
							if (j >= csvRow.length) {
								break;
							}
							
							// create key columns for additional cellsheaders
							if (createCellCounter == 0) {
								cell = row.createCell(createCellCounter++);
								cell.setCellValue(csvRow[indexNodeMOKey]);
								cell = row.createCell(createCellCounter++);
								cell.setCellValue(csvRow[indexMO]);
								cell = row.createCell(createCellCounter++);
								cell.setCellValue(csvRow[indexMocId]);
							}

							// write all other column data (except for key columns)
							if (j != indexNodeMOKey && j != indexMO && j != indexMocId) {
								
								if(createCellCounter==255) {
								String jigarviralviral = "";	
								}
								cell = row.createCell(createCellCounter++);
								cell.setCellValue(csvRow[j]);
							}
						}
					}
				}

				reader.close();
				fr.close();
			}

			File excelFile = new File(outputExcelFile);

			try {
				FileOutputStream out = new FileOutputStream(excelFile);
				workbook.write(out);
				out.close();
			}
			catch (Exception e) {
				String excelPath = excelFile != null ? excelFile.getPath() : "";
				Logger.logger.error("write exception! excelFile=" + excelPath, e);
				Logger.getGmoLogger().printError("Error writing to " + excelPath + "!");
			}

			workbook.close();
			return excelFile;
		}
		catch (Exception e) {
			Logger.logger.error("convertKgetCsvToExcelWithMultipleSheets exception! outputExcelFile=" + outputExcelFile, e);
			Logger.getGmoLogger().printError("Error converting KGET CSVs to " + outputExcelFile + "!");
			return null;
		}
	}

	/**
	 * Converts RND CIQ .xls/.xlsx to CSV and store in CM_CIQs folder 
	 * @param rndCiqFile
	 */
	public static void convertRNDToCSV(File rndCiqFile, ArrayList<String> sheetsToProcess)
	{
		try {
			// if RND is in a directory
			if (rndCiqFile.isDirectory()) {
				int fileCounter = 1;
				Set<String> sheetsWithData = new HashSet<String>();
				for (File file : rndCiqFile.listFiles()) {
					List<String> patterns = new ArrayList<String>();
					patterns.add(".*[Rr][Nn][Dd].*\\.(xls|xlsx|xlsm)");
					patterns.add("^[\\w].*\\.(xls|xlsx|xlsm)");
					if (StringUtil.matchAllPatterns(file.getName(), patterns)) {
						for (String sheet : sheetsToProcess) {
							convertCIQToCSV(file, sheet, "RNDCIQ" + fileCounter + "_" + CiqConstants.ciqSheetToCSVFileTag.get(sheet));
							sheetsWithData.add(CiqConstants.ciqSheetToCSVFileTag.get(sheet));
						}
						fileCounter++;
					}
				}
				for (String sheetWithData : sheetsWithData) {
					if (sheetWithData.equals("ENBINFO")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ[\\d]+_ENBINFO\\.csv", "RNDCIQ_ENBINFO");
					}
					else if (sheetWithData.equals("EUTRANPARAM")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ[\\d]+_EUTRANPARAM\\.csv", "RNDCIQ_EUTRANPARAM");
					}
					else if (sheetWithData.equals("PCI")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ[\\d]+_PCI\\.csv", "RNDCIQ_PCI");
					}
					else if (sheetWithData.equals("LOSSESDELAYS")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ[\\d]+_LOSSESDELAYS\\.csv", "RNDCIQ_LOSSESDELAYS");
					}
					else if (sheetWithData.equals("RET")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ[\\d]+_RET\\.csv", "RNDCIQ_RET");
					}
					else if (sheetWithData.equals("CASCADEMAP")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ[\\d]+_CASCADEMAP\\.csv", "RNDCIQ_CASCADEMAP");
					}
					else if (sheetWithData.equals("gNB Info")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ[\\d]+_GNB\\s*INFO\\.csv", "RNDCIQ_GNBINFO");
					}
					else if (sheetWithData.equals("gUtranCell info")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ[\\d]+_GUTRANCELL\\s*INFO\\.csv", "RNDCIQ_GUTRANCELLINFO");
					}
					else {
						// File csvFile = new File(FileUtil.getCmCiqDirectory() + "\\\\" + "RNDCIQ_" + sheetWithData + ".csv");
						// if (!csvFile.exists()) {
						// gmoLogger.printWarning("Create new CSV " + sheetWithData + "\\.csv");
						// }
						// else {
						// gmoLogger.println("Don't Create new CSV " + sheetWithData + "\\.csv");
						// }
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ[\\d]+_" + sheetWithData + "\\.csv", "RNDCIQ_" + sheetWithData);
					}
				}
			}
			else {
				if (sheetsToProcess != null && !sheetsToProcess.isEmpty()) {
					for (String sheet : sheetsToProcess) {
						convertCIQToCSV(rndCiqFile, sheet, "RNDCIQ_" + CiqConstants.ciqSheetToCSVFileTag.get(sheet));
					}
				}
				else {
					CSVUtils.convertCIQToCSV(rndCiqFile, "eNB Info", "RNDCIQ_ENBINFO");
					CSVUtils.convertCIQToCSV(rndCiqFile, "eUtran Parameters", "RNDCIQ_EUTRANPARAM");
					CSVUtils.convertCIQToCSV(rndCiqFile, "PCI", "RNDCIQ_PCI");
					CSVUtils.convertCIQToCSV(rndCiqFile, "Losses and Delays", "RNDCIQ_LOSSESDELAYS");
					CSVUtils.convertCIQToCSV(rndCiqFile, "Cluster", "RNDCIQ_CLUSTER");
					CSVUtils.convertCIQToCSV(rndCiqFile, "eUtran NeighRelations", "RNDCIQ_EUTRANNEIGHRELATIONS");
					CSVUtils.convertCIQToCSV(rndCiqFile, "eUtran NeighRelations co-sites", "RNDCIQ_EUTRANNEIGHRELATIONSCOSITES");
					CSVUtils.convertCIQToCSV(rndCiqFile, "([\\s]*LTE-UMTS-[uU]tranFreqRelation[\\s]*|LTE-UMTS[\\s]*\\(UtranFreqRelation\\)(_[\\d])?[\\s]*)", "RNDCIQ_LTEUMTS");
					CSVUtils.convertCIQToCSV(rndCiqFile, "([\\s]*LTE-LTE[\\s]*\\(E[uU]tranFreqRelation\\)|LTE-LTE-[\\s]*FreqRelation[\\s]*)", "RNDCIQ_LTELTE");
					CSVUtils.convertCIQToCSV(rndCiqFile, "eUtraN interfreq relations", "RNDCIQ_EUTRANINTERFREQRELATIONS");
					CSVUtils.convertCIQToCSV(rndCiqFile, "RET", "RNDCIQ_RET");
					CSVUtils.convertCIQToCSV(rndCiqFile, "LTE Carrier Aggregation", "RNDCIQ_CARRIERAGG");
					CSVUtils.convertCIQToCSV(rndCiqFile, "UMTS-LTE-Relations", "RNDCIQ_UMTSLTE");
					CSVUtils.convertCIQToCSV(rndCiqFile, "LTE-GSM-FreqGroupRel", "RNDCIQ_LTEGSM_FREQGRPREL");
					CSVUtils.convertCIQToCSV(rndCiqFile, "LTE-NR FreqRelation", "RNDCIQ_LTENR_FREQREL");
					CSVUtils.convertCIQToCSV(rndCiqFile, "LTE-GSMGeranFreqGroup", "RNDCIQ_LTEGSMGERANFREQGRP");
					CSVUtils.convertCIQToCSV(rndCiqFile, "LTE-GSM-CELLS", "RNDCIQ_LTEGSMCELLS");
					CSVUtils.convertCIQToCSV(rndCiqFile, "GSM-LTE-Relation", "RNDCIQ_GSMLTEREL");
					CSVUtils.convertCIQToCSV(rndCiqFile, "Cascaded RET Devices", "RNDCIQ_RETDEVICES");
					CSVUtils.convertCIQToCSV(rndCiqFile, ".*(Asymmetric reconfigs|Asymmetric Reconfigs|Asymmetric Configuration).*", "RNDCIQ_ASYMMETRIC");
					CSVUtils.convertCIQToCSV(rndCiqFile, "R[Ee][Tt][\\s]*Profile", "RNDCIQ_RETPROFILE");		// Updated 05/30/2019, eusxjas
//					CSVUtils.convertCIQToCSV(rndCiqFile, "RetProfile", "RNDCIQ_RETPROFILE");
					CSVUtils.convertCIQToCSV(rndCiqFile, "L2L", "RNDCIQ_L2L");
					CSVUtils.convertCIQToCSV(rndCiqFile, "L2LFREQR", "RNDCIQ_L2LFREQR");
					CSVUtils.convertCIQToCSV(rndCiqFile, "L2GFREQ", "RNDCIQ_L2GFREQ");
					CSVUtils.convertCIQToCSV(rndCiqFile, "LTE2GSM", "RNDCIQ_LTE2GSM");
					CSVUtils.convertCIQToCSV(rndCiqFile, "FDDTDDRELATION", "RNDCIQ_FDDTDDRELATION");
					CSVUtils.convertCIQToCSV(rndCiqFile, "L2GCELLS", "RNDCIQ_L2GCELLS");
					CSVUtils.convertCIQToCSV(rndCiqFile, "L2U", "RNDCIQ_L2U");
					CSVUtils.convertCIQToCSV(rndCiqFile, "L2UCELLS", "RNDCIQ_L2UCELLS");
					CSVUtils.convertCIQToCSV(rndCiqFile, "U2LFREQ", "RNDCIQ_U2LFREQ");
					CSVUtils.convertCIQToCSV(rndCiqFile, "L2UFREQ", "RNDCIQ_L2UFREQ");
					CSVUtils.convertCIQToCSV(rndCiqFile, "UMTS2LTE", "RNDCIQ_UMTS2LTE");
					CSVUtils.convertCIQToCSV(rndCiqFile, "GSM2LTE", "RNDCIQ_GSM2LTE");
					CSVUtils.convertCIQToCSV(rndCiqFile, "L2LREL", "RNDCIQ_L2LREL");
					CSVUtils.convertCIQToCSV(rndCiqFile, "L2UREL", "RNDCIQ_L2UREL");
					CSVUtils.convertCIQToCSV(rndCiqFile, "L2GREL", "RNDCIQ_L2GREL");

					CSVUtils.convertCIQToCSV(rndCiqFile, "gNB Info", "RNDCIQ_GNBINFO");
					CSVUtils.convertCIQToCSV(rndCiqFile, "gUtranCell info", "RNDCIQ_GUTRANCELLINFO");
					CSVUtils.convertCIQToCSV(rndCiqFile, "NR Carrier Aggregation", "RNDCIQ_NR_Carrier_Aggregation");
				}
			}
		}
		catch (Exception e) {
			logger.error("convertRNDToCSV exception!", e);
			gmoLogger.printError("Convert RND to CSV exception! " + e.getMessage());
		}
	}

	/**
	 * Converts RND CIQ .xls/.xlsx to CSV and store in CM_CIQs folder 
	 * @param rndCiqFile
	 */
	private void convertWcdmaRNDToCSV()
	{
		try {
			// if RND is in a directory
			if (rndCiqFile.isDirectory()) {
				int fileCounter = 1;
				Set<String> sheetsWithData = new HashSet<String>();
				for (File file : rndCiqFile.listFiles()) {
					if (StringUtil.doesMatch(file.getName(), TMOConstants.tmoUmtsRndFileNameRegex, Pattern.CASE_INSENSITIVE)) {
						for (String sheet : sheetsToProcess) {
							convertCIQToCSV(file, sheet, "RNDCIQ_WCDMA" + fileCounter + "_" + CiqConstants.ciqSheetToCSVFileTag.get(sheet));
							sheetsWithData.add(CiqConstants.ciqSheetToCSVFileTag.get(sheet));
						}
						fileCounter++;
					}
				}
				for (String sheetWithData : sheetsWithData) {
					if (sheetWithData.equals("FEEDERDELAYINFO")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_FEEDERDELAYINFO\\.csv", "RNDCIQ_WCDMA_FEEDERDELAYINFO");
					}
					else if (sheetWithData.equals("ASYMMETRIC")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_ASYMMETRIC\\.csv", "RNDCIQ_WCDMA_ASYMMETRIC");
					}
					else if (sheetWithData.equals("RBSSITE")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_RBSSITE\\.csv", "RNDCIQ_WCDMA_RBSSITE");
					}
					else if (sheetWithData.equals("DYNRN")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_DYNRN\\.csv", "RNDCIQ_WCDMA_DYNRN");
					}
					else if (sheetWithData.equals("LACSACRAC")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_LACSACRAC\\.csv", "RNDCIQ_WCDMA_LACSACRAC");
					}
					else if (sheetWithData.equals("INTRAFREQ")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_INTRAFREQ\\.csv", "RNDCIQ_WCDMA_INTRAFREQ");
					}
					else if (sheetWithData.equals("INTERFREQ")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_INTERFREQ\\.csv", "RNDCIQ_WCDMA_INTERFREQ");
					}
					else if (sheetWithData.equals("UTRANGSM")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_UTRANGSM\\.csv", "RNDCIQ_WCDMA_UTRANGSM");
					}
					else if (sheetWithData.equals("GSMNBR")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_GSMNBR\\.csv", "RNDCIQ_WCDMA_GSMNBR");
					}
					else if (sheetWithData.equals("CLUSTER")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_CLUSTER\\.csv", "RNDCIQ_WCDMA_CLUSTER");
					}
					else if (sheetWithData.equals("RETPROFILE")) {
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_RETPROFILE\\.csv", "RNDCIQ_WCDMA_RETPROFILE");
					}
					else {
						//						File csvFile = new File(FileUtil.getCmCiqDirectory() + "\\\\" + "RNDCIQ_WCDMA_" + sheetWithData + ".csv");
						//						if (!csvFile.exists()) {
						//							gmoLogger.printWarning("Create new CSV " + csvFile.getName());
						//						}
						//						else {
						//							gmoLogger.println("Don't Create new CSV " + csvFile.getName());
						//						}
						mergeCSVFilesAppendRowsEnhanced(FileUtil.getCmCiqDirectory(), "RNDCIQ_WCDMA[\\d]+_" + sheetWithData + "\\.csv", "RNDCIQ_WCDMA_" + sheetWithData);
					}
				}
			}
			else {

				// WCDMA RNDCIQ - eusxjas - 06/22/2018
				CSVUtils.convertCIQToCSV(rndCiqFile, "Feeder Delay Info", "RNDCIQ_WCDMA_FEEDERDELAYINFO");
				CSVUtils.convertCIQToCSV(rndCiqFile, "Asymmetric Configuration", "RNDCIQ_WCDMA_ASYMMETRICCONFIGURATION");
				CSVUtils.convertCIQToCSV(rndCiqFile, "RBS Site", "RNDCIQ_WCDMA_RBSSITE");
				CSVUtils.convertCIQToCSV(rndCiqFile, "dyn RN", "RNDCIQ_WCDMA_DYNRN");
				CSVUtils.convertCIQToCSV(rndCiqFile, "Lac-Sac-Rac", "RNDCIQ_WCDMA_LACSACRAC");
				CSVUtils.convertCIQToCSV(rndCiqFile, "Intra Frequency Relations", "RNDCIQ_WCDMA_INTRAFREQUENCYRELATIONS");
				CSVUtils.convertCIQToCSV(rndCiqFile, "Inter Frequency Relations", "RNDCIQ_WCDMA_INTERFREQUENCYRELATIONS");
				CSVUtils.convertCIQToCSV(rndCiqFile, "UTRAN-GSM Relation", "RNDCIQ_WCDMA_UTRANGSMRELATION");
				CSVUtils.convertCIQToCSV(rndCiqFile, "GSM Nbr Cell", "RNDCIQ_WCDMA_GSMNBRCELL");
				CSVUtils.convertCIQToCSV(rndCiqFile, "Cluster", "RNDCIQ_WCDMA_CLUSTER");
				CSVUtils.convertCIQToCSV(rndCiqFile, "RetProfile", "RNDCIQ_WCDMA_RETPROFILE");
			}
		}
		catch (Exception e) {
			logger.error("convertWcdmaRNDToCSV exception!", e);
			gmoLogger.printError("Convert WCDMA RND to CSV exception! " + e.getMessage());
		}
	}

	public static File excel2CSV(File ciqFile, String sheetName, String outputCSVFileName)
	{
		try {
			File csvFile = new File(FileUtil.getCmCiqDirectory() + File.separator + outputCSVFileName + ".csv");
			Files.deleteIfExists(csvFile.toPath());
			/*** in case ciqFile not found ***/
			if (!ciqFile.exists()) {
				return null;
			}

			// Get the workbook object for XLS/XLSX file
			Workbook workbook = WorkbookFactory.create(ciqFile, "", true);
			DataFormatter df = new DataFormatter();

			FileWriter fw = new FileWriter(csvFile.getPath());
			CSVWriter writer = new CSVWriter(fw);

			/*** Get first sheet from the workbook ***/
			Sheet sheet = null;
			for (int i = 0; i < workbook.getNumberOfSheets(); i++) {
				if (StringUtil.doesMatch(workbook.getSheetAt(i).getSheetName(), sheetName, Pattern.CASE_INSENSITIVE) && !(workbook.isSheetHidden(i) || workbook.isSheetVeryHidden(i))) {
					sheet = workbook.getSheetAt(i);
					break;
				}
			}

			/*** in case sheet not found ***/
			if (sheet == null) {
				writer.flushQuietly();
				writer.close();
				fw.close();
				workbook.close();
				Files.deleteIfExists(csvFile.toPath());
				return null;
			}

			/*** get header row size ***/
			Row headerRow = null;
			for (int i = 0; i < 10; i++) {
				headerRow = sheet.getRow(i);
				if (headerRow != null) {
					break;
				}
			}
			int headerRowSize = 0;
			if (headerRow != null) {
				headerRowSize = headerRow.getLastCellNum();
			}

			Integer numOfRows = sheet.getPhysicalNumberOfRows();
			if (numOfRows > 60000) {			// [09172020] Check for CIQs with more rows than typically found to warn the user if GMO fails to process the inputs.
				Logger.logger.warn("excel2CSV ciqFile=" + ciqFile + ", sheetName='" + sheetName + "', outputCSVFileName='" + outputCSVFileName + "', has a very large number of rows (" + numOfRows.toString() + "). If GMO fails to execute please review this sheet of the CIQ for erroneous or excessive data rows.");
				Logger.getGmoLogger().printWarning("Excel CIQ sheetName='" + sheetName + "', has a very large number of rows (" + numOfRows.toString() + "). If GMO fails to execute, please review the CIQ for erroneous or excessive data rows.");
			}
			if (headerRowSize > 200) {			// [09172020] Check for CIQs or kgets with more columns than typically found. Typically is only sheetName='EUtranCellFDD~', outputCSVFileName='KGET_EUTRANCELLFDD' with 255+ columns
				if (!sheetName.matches("EUtranCell[FT]DD.*"))  {
					Logger.logger.warn("excel2CSV ciqFile=" + ciqFile + ", sheetName='" + sheetName + "', outputCSVFileName='" + outputCSVFileName + "', has a large number of columns (" +  headerRowSize + "). If GMO fails to execute please review this sheet of the CIQ for erroneous or excessive data columns.");
				}
			}
			
			Integer consecutiveEmptyRowCount = 0;		// If too many empty rows are consecutively encountered then break importing of this sheet
			for (Row row : sheet) {
				/*** Create record ***/
				ArrayList<String> record = new ArrayList<String>();

				for (int cn = 0; cn < row.getLastCellNum(); cn++) {
					// If the cell is missing from the file, generate a blank one
					// (Works by specifying a MissingCellPolicy)
					Cell cell = row.getCell(cn, Row.CREATE_NULL_AS_BLANK);

					switch (cell.getCellType()) {
						case Cell.CELL_TYPE_BOOLEAN:
							record.add("" + cell.getBooleanCellValue());
							break;

						case Cell.CELL_TYPE_NUMERIC:
							// record.add(Double.toString(cell.getNumericCellValue()).replaceAll("\\.0+$", ""));
							record.add(df.formatCellValue(cell).replaceAll("\\.0+$", ""));
							break;

						case Cell.CELL_TYPE_STRING:
							record.add(cell.getStringCellValue().trim().replaceAll("\"", ""));
							break;

						case Cell.CELL_TYPE_BLANK:
							record.add("");
							break;

						case Cell.CELL_TYPE_FORMULA:
							switch (cell.getCachedFormulaResultType()) {
								case Cell.CELL_TYPE_NUMERIC:
									String cellStringValue = Double.toString(cell.getNumericCellValue());
									cellStringValue = cellStringValue.matches("^.*\\.0$") ? cellStringValue.replaceAll("\\.[\\d]+$", "") : cellStringValue;
									record.add(cellStringValue);
									break;
								case Cell.CELL_TYPE_STRING:
									record.add(cell.getStringCellValue().trim());
									break;
								default:
									record.add("");
									}
							break;

						default:
							record.add("" + cell);
					}
				}

				/*** padding ***/
				while (record.size() < headerRowSize) {
					record.add("");
				}

				/*** Write the record to file ***/
				if (record.size() > 0) {
					String[] newArray = new String[record.size()];
					
					Boolean addRecord = true;			// [09172020
					/*if (isTestServer && SystemConstants.userSignum.equalsIgnoreCase("eusxjas")) {	// [09172020 Check to not write files to CSV if they contain no data
						Boolean allRecordsEmpty = true;
						for(String val : record) {
							if (!val.isEmpty()) {		// If val has only '0', for example, in a column then row will not be saved. Hopefully will avoid out of memory exception for case that had over a million rows of 0 in one column
								allRecordsEmpty = false;
								if (val.length() > 1) {
									consecutiveEmptyRowCount = 0;
								}
								break;
							}
						}
						addRecord = !allRecordsEmpty;
					}*/
					
					if (addRecord) {					// [09172020
						writer.writeNext(record.toArray(newArray));
					}
					/*if (isTestServer && SystemConstants.userSignum.equalsIgnoreCase("eusxjas")){	// [09232020] If too many empty rows are consecutively encountered then break importing of this sheet
						consecutiveEmptyRowCount = consecutiveEmptyRowCount++;
						
						if (consecutiveEmptyRowCount > 1000) {
							Logger.getGmoLogger().printWarning("Excel CIQ sheetName='" + sheetName + "', has over 1000 consecutive, empty rows. GMO will discontinue importation of this CIQ sheet to avoid wasting time. Please check the CIQ and generated scripts.");
							continue;
						}
					}*/
				}
			}

			// close the writer
			writer.flushQuietly();
			writer.close();
			fw.close();

			workbook.close();
			return csvFile;
		}
		catch (Exception e) {
			String ciqPath = ciqFile != null ? ciqFile.getPath() : "";
			Logger.logger.error("excel2CSV exception! ciqFile=" + ciqPath + ", sheetName=" + sheetName + ", outputCSVFileName=" + outputCSVFileName, e);
			Logger.getGmoLogger().printError("Error converting " + ciqPath + " " + sheetName + " to " + outputCSVFileName + "!");
			return null;
		}
	}

	/**
	 * Checks if CSV file exists and not empty.
	 * @param csvFile - CSV file
	 * @param ignoreHeader - ignore 1st row of data
	 * @return TRUE if CSV file not null, exists, and not empty, otherwise FALSE
	 */
	public static boolean existsAndNotEmpty(File csvFile, boolean ignoreHeader)
	{
		boolean existsAndNotEmpty = false;
		try {
			if (csvFile != null && csvFile.exists()) {

				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				if (!allRows.isEmpty()) {

					int initIndex = 0;

					// ignore header row
					if (ignoreHeader) {
						if (initIndex < allRows.size()) {
							initIndex++;
						}
					}

					for (int i = initIndex; i < allRows.size(); i++) {
						for (String cell : allRows.get(i)) {
							if (!cell.trim().isEmpty()) {
								existsAndNotEmpty = true;
								break;
							}
						}
						if (existsAndNotEmpty) {
							break;
						}
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("existsAndNotEmpty exception! csvFile=" + csvPath, e);
			Logger.getGmoLogger().printError("Error checking if " + csvPath + " exists and not empty!");
		}

		return existsAndNotEmpty;
	}

	/**
	 * Export KGET data map to CSVs and store in CM_CIQs
	 * @param hmapKgetPoData
	 */
	private static void exportKGETDataMapToCSV(HashMap<String, List<String>> hmapKgetPoData)
	{
		try {
			/*** retrieve unique MOCs ***/
			HashMap<String, ArrayList<LinkedHashMap<String, String>>> mocToParamValueMap = new HashMap<String, ArrayList<LinkedHashMap<String, String>>>();

			List<String> uniqueMOCs = new ArrayList<String>();
			for (HashMap.Entry<String, List<String>> entry : hmapKgetPoData.entrySet()) {

				// key: 047268_WARNER!OptionalFeatureLicense!SystemFunctions=1,Licensing=1,OptionalFeatureLicense=CategoryMAccess
				String key = entry.getKey();
				String site = key.split("!")[0];
				String moc = key.split("!")[1];

				// uniqueMOCs
				if (!moc.isEmpty() && !uniqueMOCs.contains(moc)) {
					uniqueMOCs.add(moc);
				}

				// moValueList: MO!SubNetwork=ONRM_ROOT_MO,SubNetwork=MKT_047,MeContext=047268_WARNER,ManagedElement=1,SystemFunctions=1,Licensing=1,OptionalFeatureLicense=CategoryMAccess
				List<String> moValueList = entry.getValue();

				/*** Structure data for output ***/

				// paramValueMap
				LinkedHashMap<String, String> paramValueMap = new LinkedHashMap<String, String>();
				paramValueMap.put("NodeMOKey", site + "!" + moc + "!" + moValueList.get(0).replaceFirst(".*ManagedElement=[\\w]+,", ""));
				for (String moValue : moValueList) {
					try {
						if (moValue.contains("!")) {
							String mo = moValue.split("!")[0];
							String value = moValue.split("!").length > 1 ? moValue.split("!")[1] : "null";
							paramValueMap.put(mo, value);
						}
					}
					catch (Exception e) {
						Logger.logger.error("exportKGETDataMapToCSV exception in paramValueMap!", e);
					}
				}

				// paramValueMapList
				ArrayList<LinkedHashMap<String, String>> paramValueMapList = new ArrayList<LinkedHashMap<String, String>>();
				if (mocToParamValueMap.containsKey(moc)) {
					paramValueMapList = mocToParamValueMap.get(moc);
				}
				paramValueMapList.add(paramValueMap);

				// mocToParamValueMap
				mocToParamValueMap.put(moc, paramValueMapList);

			}

			// dump contents into file
			Map<String, LinkedHashMap<String, Integer>> mocHeaderIndexMap = new HashMap<String, LinkedHashMap<String, Integer>>();
			for (Map.Entry<String, ArrayList<LinkedHashMap<String, String>>> data : mocToParamValueMap.entrySet()) {
				String moc = data.getKey();

				// headerIndexMap
				LinkedHashMap<String, Integer> headerIndexMap = new LinkedHashMap<String, Integer>();
				if (mocHeaderIndexMap.containsKey(moc)) {
					headerIndexMap = mocHeaderIndexMap.get(moc);
				}

				ArrayList<LinkedHashMap<String, String>> paramValueMapList1 = data.getValue();
				StringBuilder sb = new StringBuilder();

				// calculate header index
				int index = 0;
				for (HashMap<String, String> paramValueMap1 : paramValueMapList1) {
					for (Map.Entry<String, String> data1 : paramValueMap1.entrySet()) {
						String header = data1.getKey();
						if (header != null && !header.isEmpty() && !headerIndexMap.containsKey(header)) {
							headerIndexMap.put(header, index++);
						}
					}
				}

				// write header
				for (Map.Entry<String, Integer> data1 : headerIndexMap.entrySet()) {
					sb.append("\"" + data1.getKey() + "\",");
				}
				sb.append("\n");

				// write data
				for (HashMap<String, String> paramValueMap1 : paramValueMapList1) {
					for (Map.Entry<String, Integer> data1 : headerIndexMap.entrySet()) {
						String key = data1.getKey();
						if (paramValueMap1.containsKey(key) && paramValueMap1.get(key) != null && !"null".equalsIgnoreCase(paramValueMap1.get(key))) {
							sb.append("\"" + paramValueMap1.get(key).replaceAll("\"", "'") + "\",");
						}
						else {
							sb.append("\"\",");
						}
					}
					sb.append("\n");
				}

				// write to file
				if (!moc.isEmpty()) {
					FileUtil.writeToFile(sb, FileUtil.getCmCiqDirectory() + File.separator + "KGET_" + moc.toUpperCase() + ".csv");
				}
			}

		}
		catch (Exception e) {
			logger.error("exportKGETDataMapToCSV exception!", e);
			// gmoLogger.printError("Error exporting KGET data map to CSV! " + e.getMessage());
		}
	}

	/**
	 * Export KGET data map to CSVs and store in CM_CIQs (Order of rows/columns in log file is preserved as it is)
	 * @param hmapKgetPoData
	 */
	private static void exportKGETDataMapToCSVKeepingOriginalOrder(LinkedHashMap<String, List<String>> hmapKgetPoData, String csvTargetDir)
	{
		try {
			/*** retrieve unique MOCs ***/
			LinkedHashMap<String, ArrayList<LinkedHashMap<String, String>>> mocToParamValueMap = new LinkedHashMap<String, ArrayList<LinkedHashMap<String, String>>>();

			List<String> uniqueMOCs = new ArrayList<String>();
			for (HashMap.Entry<String, List<String>> entry : hmapKgetPoData.entrySet()) {

				// key: 047268_WARNER!OptionalFeatureLicense!SystemFunctions=1,Licensing=1,OptionalFeatureLicense=CategoryMAccess
				String key = entry.getKey();
				String site = key.split("!")[0];
				String moc = key.split("!")[1];

				// uniqueMOCs
				if (!moc.isEmpty() && !uniqueMOCs.contains(moc)) {
					uniqueMOCs.add(moc);
				}

				// moValueList: MO!SubNetwork=ONRM_ROOT_MO,SubNetwork=MKT_047,MeContext=047268_WARNER,ManagedElement=1,SystemFunctions=1,Licensing=1,OptionalFeatureLicense=CategoryMAccess
				List<String> moValueList = entry.getValue();

				/*** Structure data for output ***/

				// paramValueMap
				LinkedHashMap<String, String> paramValueMap = new LinkedHashMap<String, String>();
				paramValueMap.put("NodeMOKey", site + "!" + moc + "!" + moValueList.get(0).replaceFirst(".*ManagedElement=[\\w]+,", ""));
				for (String moValue : moValueList) {
					try {
						if (moValue.contains("!")) {
							String mo = moValue.split("!")[0];
							String value = moValue.split("!").length > 1 ? moValue.split("!")[1] : "null";
							paramValueMap.put(mo, value);
						}
					}
					catch (Exception e) {
						Logger.logger.error("exportKGETDataMapToCSV exception in paramValueMap!", e);
					}
				}

				// paramValueMapList
				ArrayList<LinkedHashMap<String, String>> paramValueMapList = new ArrayList<LinkedHashMap<String, String>>();
				if (mocToParamValueMap.containsKey(moc)) {
					paramValueMapList = mocToParamValueMap.get(moc);
				}
				paramValueMapList.add(paramValueMap);

				// mocToParamValueMap
				mocToParamValueMap.put(moc, paramValueMapList);

			}

			// dump contents into file
			Map<String, LinkedHashMap<String, Integer>> mocHeaderIndexMap = new LinkedHashMap<String, LinkedHashMap<String, Integer>>();
			for (Map.Entry<String, ArrayList<LinkedHashMap<String, String>>> data : mocToParamValueMap.entrySet()) {
				String moc = data.getKey();

				// headerIndexMap
				LinkedHashMap<String, Integer> headerIndexMap = new LinkedHashMap<String, Integer>();
				if (mocHeaderIndexMap.containsKey(moc)) {
					headerIndexMap = mocHeaderIndexMap.get(moc);
				}

				ArrayList<LinkedHashMap<String, String>> paramValueMapList1 = data.getValue();
				StringBuilder sb = new StringBuilder();

				// calculate header index
				int index = 0;
				for (HashMap<String, String> paramValueMap1 : paramValueMapList1) {
					for (Map.Entry<String, String> data1 : paramValueMap1.entrySet()) {
						if (!headerIndexMap.containsKey(data1.getKey())) {
							headerIndexMap.put(data1.getKey(), index++);
						}
					}
				}

				// write header
				for (Map.Entry<String, Integer> data1 : headerIndexMap.entrySet()) {
					sb.append("\"" + data1.getKey() + "\",");
				}
				sb.append("\n");

				// write data
				for (HashMap<String, String> paramValueMap1 : paramValueMapList1) {
					for (Map.Entry<String, Integer> data1 : headerIndexMap.entrySet()) {
						String key = data1.getKey();
						if (paramValueMap1.containsKey(key) && paramValueMap1.get(key) != null && !"null".equalsIgnoreCase(paramValueMap1.get(key))) {
							sb.append("\"" + paramValueMap1.get(key) + "\",");
						}
						else {
							sb.append("\"\",");
						}
					}
					sb.append("\n");
				}

				// write to file
				if (!moc.isEmpty()) {
					FileUtil.writeToFile(sb, csvTargetDir + File.separator + "KGET_" + moc.toUpperCase() + ".csv");
				}
			}

		}
		catch (Exception e) {
			logger.error("exportKGETDataMapToCSVKeepingOriginalOrder exception!", e);
		}
	}

	/**
	 * Filter data from CSV file. If value under refCol1 doesn't match lookupValue1, then data for that row will not be included in filtered file.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @return File with rows filtered out
	 */
	public static File filterDataFromCSVFile(File csvFile, String refCol1, String lookupValue1)
	{
		File newCSVFile = null;
		try {
			if (csvFile != null && csvFile.exists()) {
				newCSVFile = new File(csvFile.getParent() + File.separator + csvFile.getName().replaceAll("\\.csv", "_Filtered.csv"));
				Files.deleteIfExists(newCSVFile.toPath());
				FileWriter fw = new FileWriter(newCSVFile.getPath());
				CSVWriter writer = new CSVWriter(fw);

				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				boolean isHeaderRow = true;
				for (String[] row : allRows) {
					/*** Create record ***/
					ArrayList<String> record = new ArrayList<String>();

					if (isHeaderRow) {
						for (int j = 0; j < row.length; j++) {
							if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							record.add(row[j]);
						}
						isHeaderRow = false;
					}
					else {
						String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";

						if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
							for (int j = 0; j < row.length; j++) {
								record.add(row[j]);
							}
						}
					}

					/*** Write the record to file ***/
					if (record.size() > 0) {
						String[] newArray = new String[record.size()];
						writer.writeNext(record.toArray(newArray));
					}
				}

				//Close
				reader.close();
				fr.close();

				// close the writer
				writer.flushQuietly();
				writer.close();
				fw.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("filterDataFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1, e);
			Logger.getGmoLogger().printError("Error filtering data from " + csvPath + "!");
		}
		return newCSVFile;
	}

	/**
	 * Filter data from CSV file.
	 * If value under refCol1/refCol2 doesn't match lookupValue1/lookupValue2, then data for that row will not be included in filtered file.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @return File with rows filtered out
	 */
	public static File filterDataFromCSVFile(File csvFile, String outDir, String refCol1, String lookupValue1, String refCol2, String lookupValue2)
	{
		File newCSVFile = null;
		try {
			if (csvFile != null && csvFile.exists()) {
				newCSVFile = new File(outDir + File.separator + csvFile.getName().substring(0, csvFile.getName().lastIndexOf(".")) + "_Filtered" + csvFile.getName().substring(csvFile.getName().lastIndexOf(".")));
				Files.deleteIfExists(newCSVFile.toPath());
				FileWriter fw = new FileWriter(newCSVFile.getPath());
				CSVWriter writer = new CSVWriter(fw);

				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				boolean isHeaderRow = true;
				for (String[] row : allRows) {
					/*** Create record ***/
					ArrayList<String> record = new ArrayList<String>();

					if (isHeaderRow) {
						for (int j = 0; j < row.length; j++) {
							if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
								refCol2Index = j;
							}
							record.add(row[j]);
						}
						isHeaderRow = false;
					}
					else {
						String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
						String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";

						if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
							if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
								for (int j = 0; j < row.length; j++) {
									record.add(row[j]);
								}
							}
						}
					}

					/*** Write the record to file ***/
					if (record.size() > 0) {
						String[] newArray = new String[record.size()];
						writer.writeNext(record.toArray(newArray));
					}
				}

				//Close
				reader.close();
				fr.close();

				// close the writer
				writer.flushQuietly();
				writer.close();
				fw.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("filterDataFromCSVFile exception! csvFile=" + csvPath + ", outDir=" + outDir + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2, e);
			Logger.getGmoLogger().printError("Error filtering data from " + csvPath + "!");
		}
		return newCSVFile;
	}

	/**
	 * Filter data from CSV file.
	 * If value under refCol1/refCol2/refCol3 doesn't match lookupValue1/lookupValue2/lookupValue3, then data for that row will not be included in filtered file.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @param refCol3 - 3rd reference column
	 * @param lookupValue3 - value to match under 3rd reference column
	 * @return File with rows filtered out
	 */
	public static File filterDataFromCSVFile(File csvFile, String outDir, String refCol1, String lookupValue1, String refCol2, String lookupValue2, String refCol3, String lookupValue3)
	{
		File newCSVFile = null;
		try {
			if (csvFile != null && csvFile.exists()) {
				newCSVFile = new File(outDir + File.separator + csvFile.getName().substring(0, csvFile.getName().lastIndexOf(".")) + "_Filtered" + csvFile.getName().substring(csvFile.getName().lastIndexOf(".")));
				Files.deleteIfExists(newCSVFile.toPath());
				FileWriter fw = new FileWriter(newCSVFile.getPath());
				CSVWriter writer = new CSVWriter(fw);

				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				int refCol3Index = -1;
				boolean isHeaderRow = true;
				for (String[] row : allRows) {
					/*** Create record ***/
					ArrayList<String> record = new ArrayList<String>();

					if (isHeaderRow) {
						for (int j = 0; j < row.length; j++) {
							if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							else if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
								refCol2Index = j;
							}
							else if (StringUtil.doesMatch(row[j], refCol3, Pattern.CASE_INSENSITIVE) && refCol3Index < 0) {
								refCol3Index = j;
							}
							record.add(row[j]);
						}
						isHeaderRow = false;
					}
					else {
						String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
						String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";
						String refVal3 = refCol3Index > -1 ? row[refCol3Index] : "";

						if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
							if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
								if (!refVal3.isEmpty() && StringUtil.doesMatch(refVal3, lookupValue3, Pattern.CASE_INSENSITIVE)) {
									for (int j = 0; j < row.length; j++) {
										record.add(row[j]);
									}
								}
							}
						}
					}

					/*** Write the record to file ***/
					if (record.size() > 0) {
						String[] newArray = new String[record.size()];
						writer.writeNext(record.toArray(newArray));
					}
				}

				//Close
				reader.close();
				fr.close();

				// close the writer
				writer.flushQuietly();
				writer.close();
				fw.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("filterDataFromCSVFile exception! csvFile=" + csvPath + ", outDir=" + outDir + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2 + ", refCol3=" + refCol3 + ", lookupValue3=" + lookupValue3, e);
			Logger.getGmoLogger().printError("Error filtering data from " + csvPath + "!");
		}
		return newCSVFile;
	}

	/**
	 * Filter data from CSV file.
	 * If value under refCol1/refCol2/refCol3/refCol4 doesn't match lookupValue1/lookupValue2/lookupValue3/lookupValue4, then data for that row will not be included in filtered file.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @param refCol3 - 3rd reference column
	 * @param lookupValue3 - value to match under 3rd reference column
	 * @param refCol4 - 4th reference column
	 * @param lookupValue4 - value to match under 4th reference column
	 * @return File with rows filtered out
	 */
	public static File filterDataFromCSVFile(File csvFile, String outDir, String refCol1, String lookupValue1, String refCol2, String lookupValue2, String refCol3, String lookupValue3, String refCol4, String lookupValue4)
	{
		File newCSVFile = null;
		try {
			if (csvFile != null && csvFile.exists()) {
				newCSVFile = new File(outDir + File.separator + csvFile.getName().substring(0, csvFile.getName().lastIndexOf(".")) + "_Filtered" + csvFile.getName().substring(csvFile.getName().lastIndexOf(".")));
				Files.deleteIfExists(newCSVFile.toPath());
				FileWriter fw = new FileWriter(newCSVFile.getPath());
				CSVWriter writer = new CSVWriter(fw);

				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				int refCol3Index = -1;
				int refCol4Index = -1;
				boolean isHeaderRow = true;
				for (String[] row : allRows) {
					/*** Create record ***/
					ArrayList<String> record = new ArrayList<String>();

					if (isHeaderRow) {
						for (int j = 0; j < row.length; j++) {
							if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							else if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
								refCol2Index = j;
							}
							else if (StringUtil.doesMatch(row[j], refCol3, Pattern.CASE_INSENSITIVE) && refCol3Index < 0) {
								refCol3Index = j;
							}
							else if (StringUtil.doesMatch(row[j], refCol4, Pattern.CASE_INSENSITIVE) && refCol4Index < 0) {
								refCol4Index = j;
							}
							record.add(row[j]);
						}
						isHeaderRow = false;
					}
					else {
						String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
						String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";
						String refVal3 = refCol3Index > -1 ? row[refCol3Index] : "";
						String refVal4 = refCol4Index > -1 ? row[refCol4Index] : "";

						if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
							if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
								if (!refVal3.isEmpty() && StringUtil.doesMatch(refVal3, lookupValue3, Pattern.CASE_INSENSITIVE)) {
									if (!refVal4.isEmpty() && StringUtil.doesMatch(refVal4, lookupValue4, Pattern.CASE_INSENSITIVE)) {
										for (int j = 0; j < row.length; j++) {
											record.add(row[j]);
										}
									}
								}
							}
						}
					}

					/*** Write the record to file ***/
					if (record.size() > 0) {
						String[] newArray = new String[record.size()];
						writer.writeNext(record.toArray(newArray));
					}
				}

				//Close
				reader.close();
				fr.close();

				// close the writer
				writer.flushQuietly();
				writer.close();
				fw.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("filterDataFromCSVFile exception! csvFile=" + csvPath + ", outDir=" + outDir + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2 + ", refCol3=" + refCol3 + ", lookupValue3=" + lookupValue3 + ", refCol4=" + refCol4 + ", lookupValue4=" + lookupValue4, e);
			Logger.getGmoLogger().printError("Error filtering data from " + csvPath + "!");
		}
		return newCSVFile;
	}

	/**
	 * Filter data from txt file. If value under refCol1 doesn't match lookupValue1, then data for that row will not be included in filtered file.
	 * 
	 * @param csvFile - txt file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @return File with rows filtered out
	 */
	public static File filterDataFromTxtFile(File txtFile, String outDir, String refCol1, String lookupValue1, String refCol2, String lookupValue2)
	{
		File newCSVFile = null;
		try (BufferedReader br = new BufferedReader(new FileReader(txtFile))) {
			newCSVFile = new File(outDir + File.separator + txtFile.getName().substring(0, txtFile.getName().lastIndexOf(".")) + "_Filtered.csv");
			Files.deleteIfExists(newCSVFile.toPath());
			FileWriter fw = new FileWriter(newCSVFile.getPath());
			CSVWriter writer = new CSVWriter(fw);

			String line;

			/*** initialize column index ***/
			int refCol1Index = -1;
			int refCol2Index = -1;
			boolean isHeaderRow = true;
			while ((line = br.readLine()) != null) {
				/*** Create record ***/
				ArrayList<String> record = new ArrayList<String>();

				if (isHeaderRow) {
					for (int j = 0; j < line.split("\t").length; j++) {
						if (StringUtil.doesMatch(line.split("\t")[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (StringUtil.doesMatch(line.split("\t")[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
							refCol2Index = j;
						}
						record.add(line.split("\t")[j]);
					}
					isHeaderRow = false;
				}
				else {
					String refVal1 = refCol1Index > -1 ? line.split("\t")[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? line.split("\t")[refCol2Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
							for (int j = 0; j < line.split("\t").length; j++) {
								record.add(line.split("\t")[j]);
							}
						}
					}
				}

				/*** Write the record to file ***/
				if (record.size() > 0) {
					String[] newArray = new String[record.size()];
					writer.writeNext(record.toArray(newArray));
				}
			}

			// close
			writer.flushQuietly();
			writer.close();
			fw.close();
		}
		catch (Exception e) {
			String txtPath = txtFile != null ? txtFile.getPath() : "";
			Logger.logger.error("filterDataFromTxtFile exception! txtFile=" + txtPath + ", outDir=" + outDir + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2, e);
			Logger.getGmoLogger().printError("Error filtering data from " + txtPath + "!");
		}
		return newCSVFile;
	}

	/**
	 * Filter out non-header rows.
	 * @param csvFile - CSV file
	 * @return File with non-header rows filtered out
	 */
	public static File filterNonHeaderRows(File csvFile)
	{
		File newCSVFile = null;
		try {
			if (csvFile != null && csvFile.exists()) {
				newCSVFile = new File(csvFile.getParent() + File.separator + csvFile.getName().replaceAll("\\.csv", "_Filtered.csv"));
				Files.deleteIfExists(newCSVFile.toPath());
				FileWriter fw = new FileWriter(newCSVFile.getPath());
				CSVWriter writer = new CSVWriter(fw);

				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize ***/
				boolean headerRowFound = false;

				for (String[] row : allRows) {

					/*** algorithm to determine if row is actual header row ***/
					if (!headerRowFound) {
						int noOfCellsWithData = 0;
						for (int j = 0; j < row.length; j++) {
							if (!row[j].isEmpty()) {
								noOfCellsWithData++;
							}
						}
						if (noOfCellsWithData / row.length < .5) {
							continue;
						}
						else {
							headerRowFound = true;
						}
					}

					/*** Create record ***/
					ArrayList<String> record = new ArrayList<String>();

					for (int j = 0; j < row.length; j++) {
						record.add(row[j]);
					}

					/*** Write the record to file ***/
					if (record.size() > 0) {
						String[] newArray = new String[record.size()];
						writer.writeNext(record.toArray(newArray));
					}
				}

				// Close
				reader.close();
				fr.close();

				// close the writer
				writer.flushQuietly();
				writer.close();
				fw.close();
			}

			// cleanup
			newCSVFile = FileUtil.replaceFile(csvFile, newCSVFile);
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("filterNonHeaderRows exception! csvFile=" + csvPath, e);
			Logger.getGmoLogger().printError("Error filtering non-header rows from " + csvPath + "!");
		}
		return newCSVFile;
	}

	/**
	 * Filter out non-header rows by using header keys as reference
	 * @param csvFile - CSV file
	 * @param headerKeys - if row contains all headerKeys then it's header row
	 * @return File with non-header rows filtered out
	 */
	public static File filterNonHeaderRows(File csvFile, List<String> headerKeys)
	{
		File newCSVFile = null;
		try {
			if (csvFile != null && csvFile.exists()) {
				newCSVFile = new File(csvFile.getParent() + File.separator + csvFile.getName().replaceAll("\\.csv", "_Filtered.csv"));
				Files.deleteIfExists(newCSVFile.toPath());
				FileWriter fw = new FileWriter(newCSVFile.getPath());
				CSVWriter writer = new CSVWriter(fw);

				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize ***/
				boolean headerRowFound = false;

				for (String[] row : allRows) {

					/*** algorithm to determine if row is actual header row ***/
					if (!headerRowFound) {
						boolean matchedAllHeaderKeys = true;
						for (String headerKey : headerKeys) {
							if (Arrays.asList(row).indexOf(headerKey) < 0) {
								matchedAllHeaderKeys = false;
								break;
							}
						}
						if (!matchedAllHeaderKeys) {
							continue;
						}
						else {
							headerRowFound = true;
						}
					}

					/*** Create record ***/
					ArrayList<String> record = new ArrayList<String>();

					for (int j = 0; j < row.length; j++) {
						record.add(row[j]);
					}

					/*** Write the record to file ***/
					if (record.size() > 0) {
						String[] newArray = new String[record.size()];
						writer.writeNext(record.toArray(newArray));
					}
				}

				// Close
				reader.close();
				fr.close();

				// close the writer
				writer.flushQuietly();
				writer.close();
				fw.close();
			}

			// cleanup
			newCSVFile = FileUtil.replaceFile(csvFile, newCSVFile);
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("filterNonHeaderRows exception! csvFile=" + csvPath + ", headerKeys=" + headerKeys.toString(), e);
			Logger.getGmoLogger().printError("Error filtering non-header rows from " + csvPath + "!");
		}
		return newCSVFile;
	}

	/**
	 * Filter out non-header rows by using header keys as reference
	 * @param csvFile - CSV file
	 * @param headerKeys - if row contains all headerKeys then it's header row
	 * @return File with non-header rows filtered out
	 */
	public static File filterNonHeaderRowswithregex(File csvFile, List<String> headerKeys)
	{
		File newCSVFile = null;
		try {
			if (csvFile != null && csvFile.exists()) {
				newCSVFile = new File(csvFile.getParent() + File.separator + csvFile.getName().replaceAll("\\.csv", "_Filtered.csv"));
				Files.deleteIfExists(newCSVFile.toPath());
				FileWriter fw = new FileWriter(newCSVFile.getPath());
				CSVWriter writer = new CSVWriter(fw);

				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize ***/
				boolean headerRowFound = false;

				for (String[] row : allRows) {

					/*** algorithm to determine if row is actual header row ***/
					if (!headerRowFound) {
					//	boolean matchedAllHeaderKeys = true;
						for (String headerKey : headerKeys) {
							if (Arrays.asList(row).toString().matches(".*"+headerKey+".*")) {
								headerRowFound = true;
								break;
							}
						}

						if (!headerRowFound) {
							continue;
						}
					}

					/*** Create record ***/
					ArrayList<String> record = new ArrayList<String>();

					for (int j = 0; j < row.length; j++) {
						record.add(row[j]);
					}

					/*** Write the record to file ***/
					if (record.size() > 0) {
						String[] newArray = new String[record.size()];
						writer.writeNext(record.toArray(newArray));
					}
				}

				// Close
				reader.close();
				fr.close();

				// close the writer
				writer.flushQuietly();
				writer.close();
				fw.close();
			}

			// cleanup
			newCSVFile = FileUtil.replaceFile(csvFile, newCSVFile);
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("filterNonHeaderRows exception! csvFile=" + csvPath + ", headerKeys=" + headerKeys.toString(), e);
			Logger.getGmoLogger().printError("Error filtering non-header rows from " + csvPath + "!");
		}
		return newCSVFile;
	}

	public File fixConvertedRNDCIQ(String inputDir)
	{
		File fixedConvertedRNDFile = null;
		try {
			/*** fix data ***/
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "1st DU type", ".*52.*", "BBU5216");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "1st DU type", ".*6630.*", "BBU6630");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU", "", "NO");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 1", "NA", "");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 2", "NA", "");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 3", "NA", "");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 1", "N/A", "");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 2", "N/A", "");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 3", "N/A", "");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 1", "na", "");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 2", "na", "");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 3", "na", "");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 1", "n/a", "");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 2", "n/a", "");
			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "2nd XMU Port 3", "n/a", "");

			/*** merge data in CSVs back to RND CIQ ***/
			LinkedHashMap<File, String> csvFileToSheetName = new LinkedHashMap<File, String>();
			if (getCIQCSVFile("RNDCIQ_ENBINFO") != null) {
				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_ENBINFO"), "eNB Info");
			}
			if (getCIQCSVFile("RNDCIQ_EUTRANPARAM") != null) {
				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "eUtran Parameters");
			}
			if (getCIQCSVFile("RNDCIQ_PCI") != null) {
				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_PCI"), "PCI");
			}
			if (getCIQCSVFile("RNDCIQ_LOSSESDELAYS") != null) {
				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_LOSSESDELAYS"), "Losses and Delays");
			}
			if (getCIQCSVFile("RNDCIQ_CLUSTER") != null) {
				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_CLUSTER"), "Cluster");
			}
			if (getCIQCSVFile("RNDCIQ_EUTRANNEIGHRELATIONS") != null) {
				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_EUTRANNEIGHRELATIONS"), "eUtran NeighRelations");
			}
			if (getCIQCSVFile("RNDCIQ_EUTRANNEIGHRELATIONSCOSITES") != null) {
				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_EUTRANNEIGHRELATIONSCOSITES"), "eUtran NeighRelations co-sites");
			}
			if (getCIQCSVFile("RNDCIQ_LTEUMTS") != null) {
				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_LTEUMTS"), "LTE-UMTS (UtranFreqRelation)");
			}
			if (getCIQCSVFile("RNDCIQ_LTELTE") != null) {
				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_LTELTE"), "LTE-LTE (EUtranFreqRelation)");
			}
			if (getCIQCSVFile("RNDCIQ_EUTRANINTERFREQRELATIONS") != null) {
				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_EUTRANINTERFREQRELATIONS"), "eUtraN interfreq relations");
			}
			fixedConvertedRNDFile = CSVUtils.convertCSVToExcel(csvFileToSheetName, inputDir + File.separator + "RNDCIQ_fixed.xls");

			// cleanup
			fixedConvertedRNDFile = FileUtil.replaceFile(new File(inputDir + File.separator + "RNDCIQ.xls"), fixedConvertedRNDFile);
		}
		catch (Exception e) {
			logger.error("fixConvertedRNDCIQ exception!", e);
			gmoLogger.printError("Fix converted RND CIQ exception! " + e.getMessage());
		}

		return fixedConvertedRNDFile;
	}

	/**
	 * Fix data in CSV file. If value under refCol1 matches lookupValue1, then replace that data with replaceValue1.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @return File with fixed data
	 */
	public File fixDataInColumnInCSVFile(File csvFile, String refCol1, String lookupValue1, String replaceValue1)
	{
		File newCSVFile = null;
		try {
			if (csvFile != null && csvFile.exists()) {
				newCSVFile = new File(csvFile.getParent() + File.separator + csvFile.getName().replaceAll("\\.csv", "_Fixed.csv"));
				Files.deleteIfExists(newCSVFile.toPath());
				FileWriter fw = new FileWriter(newCSVFile.getPath());
				CSVWriter writer = new CSVWriter(fw);

				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				boolean isHeaderRow = true;
				for (String[] row : allRows) {
					/*** Create record ***/
					ArrayList<String> record = new ArrayList<String>();

					if (isHeaderRow) {
						for (int j = 0; j < row.length; j++) {
							if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							record.add(row[j]);
						}
						isHeaderRow = false;
					}
					else {
						for (int j = 0; j < row.length; j++) {
							if (j == refCol1Index && StringUtil.doesMatch(row[refCol1Index], lookupValue1, Pattern.CASE_INSENSITIVE)) {
								record.add(replaceValue1);
							}
							else {
								record.add(row[j]);
							}
						}
					}

					/*** Write the record to file ***/
					if (record.size() > 0) {
						String[] newArray = new String[record.size()];
						writer.writeNext(record.toArray(newArray));
					}
				}

				//Close
				reader.close();
				fr.close();

				// close the writer
				writer.flushQuietly();
				writer.close();
				fw.close();

				// cleanup
				newCSVFile = FileUtil.replaceFile(csvFile, newCSVFile);
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("fixDataInColumnInCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", replaceValue1=" + replaceValue1, e);
			Logger.getGmoLogger().printError("Error fixing data in " + refCol1 + " for " + csvPath + "!");
		}
		return newCSVFile;
	}

	/**
	 * Function to convert hashtable of parsed kget into individual CSVs
	 * @param poData
	 */
	public static void hashToCsvWorkbook(Hashtable<String, List<String>> poData)
	{
		try {
			HashMap<String, List<String>> hmapKgetPoData = new HashMap<String, List<String>>(poData);
			exportKGETDataMapToCSV(hmapKgetPoData);
		}
		catch (Exception e) {
			logger.error("hashToCsvWorkbook exception!", e);
		}
	}

	/**
	 * Function to convert hashtable of parsed kget into individual CSVs (Order of rows/columns in log file is preserved as it is)
	 * @param poData 
	 */
	public static void hashToCsvWorkbookKeepingOriginalOrder(Hashtable<String, List<String>> poData, String csvTargetDir)
	{
		try {
			LinkedHashMap<String, List<String>> hmapKgetPoData = new LinkedHashMap<String, List<String>>(poData);
			exportKGETDataMapToCSVKeepingOriginalOrder(hmapKgetPoData, csvTargetDir);
		}
		catch (Exception e) {
			logger.error("hashToCsvWorkbookKeepingOriginalOrder exception!", e);
		}
	}
	
	/**
	 * Initialize data from IMOMD and store in HashMap
	 */
	public static void initDataFromIMOMD(File iMOMD)
	{
		mocParamToDefaultValue = new HashMap<String, String>();
		try {
			/*** mocParamToDefaultValue ***/
			BufferedReader br = new BufferedReader(new FileReader(iMOMD));
			String line;
			while ((line = br.readLine()) != null) {
				if (StringUtil.doesMatch(line, "[\\s]*attr_description.*", Pattern.CASE_INSENSITIVE)) {
					String moc = line.trim().replaceAll(".*attr_description\\[Lrat\\.", "").replaceAll(",.*", "");
					String param = line.trim().replaceAll(".*attr_description\\[Lrat\\.[\\w]+,", "").replaceAll("\\].*", "");
					String defaultValue = line.trim().replaceAll(".*>Default=", "").replaceAll("<.*", "");
					mocParamToDefaultValue.put(moc + "!" + param, defaultValue);
				}
			}
			if (br != null) {
				br.close();
			}
		}
		catch (Exception e) {
			logger.error("initDataFromIMOMD exception!", e);
			gmoLogger.printError("Init data from IMOMD exception! " + e.getMessage());
		}
	}

	private void initializeCACIQ()
	{
		try {
			caENodeBCSV = convertCIQToCSV(ciqs.get("CACIQ"), "eNodeB", "CACIQ_ENODEB");
			caDynRnCSV = convertCIQToCSV(ciqs.get("CACIQ"), "dyn RN", "CACIQ_DYNRN");
			caRachRootSequenceCSV = convertCIQToCSV(ciqs.get("CACIQ"), "rachrootsequence", "CACIQ_RACHROOTSEQUENCE");
		}
		catch (Exception e) {
			logger.error("initializeCACIQ exception!", e);
			gmoLogger.printError("Initialize CACIQ exception! " + e.getMessage());
		}
	}

	private void initializeRND()
	{
		try {
			rndCiqFile = ciqs.get("RND");
			convertRNDToCSV(rndCiqFile, sheetsToProcess);
		}
		catch (Exception e) {
			logger.error("initializeRND exception!", e);
			gmoLogger.printError("Initialize RND exception! " + e.getMessage());
		}
	}

	private void initializeWcdmaRND()
	{
		try {
			rndCiqFile = ciqs.get("WCDMA");
			convertWcdmaRNDToCSV();
		}
		catch (Exception e) {
			logger.error("initializeWcdmaRND exception!", e);
			gmoLogger.printError("Initialize WCDMA RND exception! " + e.getMessage());
		}
	}

	private void initializeKGET(List<String> mocList)
	{
		try {
			Set<String> combinedSetMOCListForCSVLogic = new LinkedHashSet<>(CiqConstants.mocListForCSVLogic);
			combinedSetMOCListForCSVLogic.addAll(CiqConstants.mocListForWCDMACSVLogic);
			List<String> combinedListMOCListForCSVLogic = new ArrayList<>(combinedSetMOCListForCSVLogic);
			if (ciqs.containsKey("KGET")) {
				if (mocList != null && !mocList.isEmpty()) {
					populateMOCToKgetCsvFile(ciqs.get("KGET"), mocList);
				}
				else {
					populateMOCToKgetCsvFile(ciqs.get("KGET"), combinedListMOCListForCSVLogic);
				}
			}
			if (ciqs.containsKey("GSM")) {
				populateMOCToKgetCsvFile(ciqs.get("GSM"), CiqConstants.mocListForGSMCSVLogic);
			}
		}
		catch (Exception e) {
			logger.error("initializeKGET exception!", e);
			gmoLogger.printError("Initialize KGET exception! " + e.getMessage());
		}
	}
	
	private void initializeGSMData()
	{
		try {
			if (ciqs.containsKey("GSM")) {
				populateMOCToKgetCsvFile(ciqs.get("GSM"), CiqConstants.mocListForGSMCSVLogic);
			}
		}
		catch (Exception e) {
			logger.error("initializeGSMData exception!", e);
			gmoLogger.printError("Initialize GSM Data exception! " + e.getMessage());
		}
	}

	/**
	 * Checks for 'invalid' data under refCol1 that doesn't match lookupValue1
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @return true if invalid data exists, otherwise false
	 */
	public boolean invalidDataExistsInCSVFile(File csvFile, String refCol1, String lookupValue1)
	{
		boolean invalidDataExists = false;
		try {
			if (csvFile != null && csvFile.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				boolean isHeaderRow = true;
				for (String[] row : allRows) {
					if (isHeaderRow) {
						for (int j = 0; j < row.length; j++) {
							if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
						}
						isHeaderRow = false;
					}
					else {
						String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";

						if (!StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
							invalidDataExists = true;
						}
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("invalidDataExistsInCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1, e);
			Logger.getGmoLogger().printError("Error checking if invalid data exists in " + csvPath + "!");
		}
		return invalidDataExists;
	}

	/**
	 * Merge CSV files (currently supports up to 2 files) by appending columns. Must have same row data structure (i.e. same rows)
	 * TODO: need to enhance to support more than 2 CSV files.
	 * 
	 * @param csvFiles - array of CSV files to merge where 1st file in array is the reference file
	 * @param mergedFileName - merged CSV file name
	 * @return
	 */
	public static File mergeCSVFilesAppendColumns(File[] csvFiles, String mergedFileName)
	{
		File newCSVFile = null;
		try {
			if (csvFiles == null || csvFiles.length == 0) {
				return newCSVFile;
			}

			newCSVFile = new File(csvFiles[0].getParent() + File.separator + mergedFileName + ".csv");
			Files.deleteIfExists(newCSVFile.toPath());
			FileWriter fw = new FileWriter(newCSVFile.getPath());
			CSVWriter writer = new CSVWriter(fw);

			//for (int i=0; i<csvFiles.length; i++) {
			//Build reader instance
			FileReader fr1 = new FileReader(csvFiles[0]);
			CSVReader reader1 = constructCSVReader(fr1, 0);
			FileReader fr2 = new FileReader(csvFiles[1]);
			CSVReader reader2 = constructCSVReader(fr2, 0);

			//Read all rows at once
			List<String[]> allRows1 = reader1.readAll();
			List<String[]> allRows2 = reader2.readAll();

			for (int k = 0; k < allRows1.size(); k++) {
				/*** Create record ***/
				ArrayList<String> record = new ArrayList<String>();
				String[] row1 = allRows1.get(k);
				String[] row2 = allRows2.get(k);

				for (int j = 0; j < row1.length; j++) {
					record.add(row1[j]);
				}
				for (int j = 0; j < row2.length; j++) {
					record.add(row2[j]);
				}

				/*** Write the record to file ***/
				if (record.size() > 0) {
					String[] newArray = new String[record.size()];
					writer.writeNext(record.toArray(newArray));
				}
			}

			//Close
			reader1.close();
			fr1.close();
			reader2.close();
			fr2.close();

			//Close
			//Files.deleteIfExists(csvFiles[i].toPath());
			//}

			// close the writer
			writer.flushQuietly();
			writer.close();
			fw.close();
		}
		catch (Exception e) {
			Logger.logger.error("mergeCSVFilesAppendColumns exception! mergedFileName=" + mergedFileName, e);
			Logger.getGmoLogger().printError("Error merging CSV files!");
		}
		return newCSVFile;
	}

	/**
	 * Merge CSV files by appending rows. Must have same column data structure (i.e. same columns)
	 * 
	 * @param csvFile - CSV file
	 * @return File with non-header rows filtered out
	 */
	public static File mergeCSVFilesAppendRows(String inputDirPath, String regexFilesMerge, String mergedOutputFile)
	{
		File newCSVFile = null;
		try {
			File inputDir = new File(inputDirPath);
			if (inputDir == null || !inputDir.isDirectory()) {
				return newCSVFile;
			}

			newCSVFile = new File(inputDir + File.separator + mergedOutputFile + ".csv");
			Files.deleteIfExists(newCSVFile.toPath());
			FileWriter fw = new FileWriter(newCSVFile.getPath());
			CSVWriter writer = new CSVWriter(fw);

			List<String[]> headerRows = new ArrayList<String[]>();

			File[] files = inputDir.listFiles();
			for (File file : files) {
				int rowCounter = 0;
				if (StringUtil.doesMatch(file.getName(), ".+\\.csv", Pattern.CASE_INSENSITIVE) && StringUtil.doesMatch(file.getName(), regexFilesMerge, Pattern.CASE_INSENSITIVE)) {
					// Build reader instance
					FileReader fr = new FileReader(file);
					CSVReader reader = constructCSVReader(fr, 0);

					// Read all rows at once
					List<String[]> allRows = reader.readAll();

					for (String[] row : allRows) {
						/*** skip empty rows ***/
						boolean rowHasData = false;
						for (String cell : row) {
							if (!cell.isEmpty()) {
								rowHasData = true;
							}
						}
						if (!rowHasData) {
							continue;
						}

						/*** algorithm to skip additional headers ***/
						boolean writeRowData = true;
						if (rowCounter++ < 1) {
							for (String[] headerRow : headerRows) {
								if (Arrays.equals(headerRow, row)) {
									writeRowData = false;
								}
							}
							headerRows.add(row);
						}

						if (writeRowData) {
							/*** Create record ***/
							ArrayList<String> record = new ArrayList<String>();

							for (int j = 0; j < row.length; j++) {
								record.add(row[j]);
							}

							/*** Write the record to file ***/
							if (record.size() > 0) {
								String[] newArray = new String[record.size()];
								writer.writeNext(record.toArray(newArray));
							}
						}
					}

					// Close
					reader.close();
					fr.close();

					// Close
					Files.deleteIfExists(file.toPath());
				}
			}

			// close the writer
			writer.flushQuietly();
			writer.close();
			fw.close();
		}
		catch (Exception e) {
			Logger.logger.error("mergeCSVFilesAppendRows exception! inputDirPath=" + inputDirPath + ", regexFilesMerge=" + regexFilesMerge + ", mergedOutputFile=" + mergedOutputFile, e);
			Logger.getGmoLogger().printError("Error merging " + regexFilesMerge + " CSV files! Please check " + inputDirPath + " and try again.");
		}
		return newCSVFile;
	}

	/**
	 * Merge CSV files by appending rows where column data structure may be different
	 * @param csvFile - CSV file
	 * @return File with non-header rows filtered out
	 */
	public static File mergeCSVFilesAppendRowsEnhanced(String inputDirPath, String regexFilesMerge, String mergedOutputFile)
	{
		File newCSVFile = null;
		try {
			File inputDir = new File(inputDirPath);
			if (inputDir == null || !inputDir.isDirectory()) {
				return newCSVFile;
			}

			newCSVFile = new File(inputDir + File.separator + mergedOutputFile + ".csv");
			Files.deleteIfExists(newCSVFile.toPath());

			// Build finalHeaderToColumnIndex
			Map<String, Integer> finalHeaderToColumnIndex = new HashMap<String, Integer>();
			int columnIndex = 0;
			File[] files = inputDir.listFiles();
			for (File file : files) {
				if (StringUtil.doesMatch(file.getName(), ".+\\.csv", Pattern.CASE_INSENSITIVE) && StringUtil.doesMatch(file.getName(), regexFilesMerge, Pattern.CASE_INSENSITIVE)) {
					FileReader fr = new FileReader(file);
					CSVReader reader = constructCSVReader(fr, 0);
					List<String[]> allRows = reader.readAll();
					if (!allRows.isEmpty()) {
						String[] headerRow = allRows.get(0);
						for (String cell : headerRow) {
							if (!finalHeaderToColumnIndex.containsKey(cell)) {
								finalHeaderToColumnIndex.put(cell, columnIndex++);
							}
						}
					}
					reader.close();
					fr.close();
				}
			}

			// initialize writer
			FileWriter fw = new FileWriter(newCSVFile.getPath());
			CSVWriter writer = new CSVWriter(fw);

			// write header first
			String[] record = new String[finalHeaderToColumnIndex.size()];
			for (Map.Entry<String, Integer> entry : finalHeaderToColumnIndex.entrySet()) {
				String header = entry.getKey();
				int index = entry.getValue();
				record[index] = header;
			}
			writer.writeNext(record);

			// then write data
			for (File file : files) {
				if (StringUtil.doesMatch(file.getName(), ".+\\.csv", Pattern.CASE_INSENSITIVE) && StringUtil.doesMatch(file.getName(), regexFilesMerge, Pattern.CASE_INSENSITIVE)) {
					Map<Integer, String> columnIndexToHeader = new HashMap<Integer, String>();
					Map<String, String> columnHeaderToValue = new HashMap<String, String>();
					FileReader fr = new FileReader(file);
					CSVReader reader = constructCSVReader(fr, 0);
					List<String[]> allRows = reader.readAll();
					for (String[] row : allRows) {
						/*** skip empty rows ***/
						boolean rowHasData = false;
						for (String cell : row) {
							if (!cell.isEmpty()) {
								rowHasData = true;
							}
						}
						if (!rowHasData) {
							continue;
						}

						/*** build columnIndexToHeader ***/
						if (columnIndexToHeader.isEmpty()) {
							for (int i = 0; i < row.length; i++) {
								columnIndexToHeader.put(i, row[i]);
							}
							continue;
						}
						else {
							for (int i = 0; i < row.length; i++) {
								columnHeaderToValue.put(columnIndexToHeader.get(i), row[i]);
							}
						}

						/*** Create record ***/
						record = new String[finalHeaderToColumnIndex.size()];
						for (Map.Entry<String, Integer> entry : finalHeaderToColumnIndex.entrySet()) {
							String header = entry.getKey();
							int index = entry.getValue();
							if (columnHeaderToValue.containsKey(header)) {
								record[index] = columnHeaderToValue.get(header);
							}
							else {
								record[index] = "";
							}
						}

						/*** Write the record to file ***/
						writer.writeNext(record);
					}

					reader.close();
					fr.close();
					Files.deleteIfExists(file.toPath());
				}
			}

			// close the writer
			writer.flushQuietly();
			writer.close();
			fw.close();
		}
		catch (Exception e) {
			Logger.logger.error("mergeCSVFilesAppendRowsEnhanced exception! inputDirPath=" + inputDirPath + ", regexFilesMerge=" + regexFilesMerge + ", mergedOutputFile=" + mergedOutputFile, e);
			Logger.getGmoLogger().printError("Error merging " + regexFilesMerge + " CSV files! Please check " + inputDirPath + " and try again.");
		}
		return newCSVFile;
	}

	/**
	 * Merge non-master header rows to the master row by using header keys as reference.
	 * Final header row will be prefixed with information of previous non-master header rows.
	 * 
	 * @param csvFile - CSV file
	 * @param headerKeys - if row contains all headerKeys then it's header row
	 * @return File with non-header rows filtered out
	 */
	public static File mergeHeaderRows(File csvFile, List<String> headerKeys)
	{
		File newCSVFile = null;
		try {
			if (csvFile != null && csvFile.exists()) {
				newCSVFile = new File(csvFile.getParent() + File.separator + csvFile.getName().replaceAll("\\.csv", "_MergedHeader.csv"));
				Files.deleteIfExists(newCSVFile.toPath());
				FileWriter fw = new FileWriter(newCSVFile.getPath());
				CSVWriter writer = new CSVWriter(fw);

				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize ***/
				boolean headerRowFound = false;
				List<String> headerRowPrefix = new ArrayList<String>();
				
				for (String[] row : allRows) {

					/*** algorithm to determine if row is actual header row ***/
					if (!headerRowFound) {
						boolean matchedAllHeaderKeys = true;
						for (String headerKey : headerKeys) {
							if (Arrays.asList(row).indexOf(headerKey) < 0) {
								matchedAllHeaderKeys = false;
								break;
							}
						}
						if (!matchedAllHeaderKeys) {
							String str = "";
							for (int k = 0; k < row.length; k++) {
								if (!row[k].isEmpty()) {
									str = row[k].trim();
								}

								// 1. update entry in headerRowPrefix if existing
								if ((headerRowPrefix.size() > k) && !headerRowPrefix.get(k).trim().isEmpty() && !str.isEmpty()) {
									headerRowPrefix.set(k, headerRowPrefix.get(k).trim() + "_" + str);
								}
								// 2. otherwise add new entry
								else {
									headerRowPrefix.add(str);
								}
							}
							continue;
						}
						else {
							// initialize lastKnownHeaderRowPrefix
							String lastKnownHeaderRowPrefix = "";

							// iterate over all columns of master header row (k is column index)
							for (int k = 0; k < row.length; k++) {

								// make sure k is less than headerRowPrefix index 
								if (k < headerRowPrefix.size()) {
									// save value to lastKnownHeaderRowPrefix
									lastKnownHeaderRowPrefix = headerRowPrefix.get(k);
								}
								
								// if lastKnownHeaderRowPrefix is not empty then append in front of master header value
								if (!lastKnownHeaderRowPrefix.isEmpty()) {
									row[k] = lastKnownHeaderRowPrefix + "_" + row[k];
								}
							}
							headerRowFound = true;
						}
					}

					/*** Create record ***/
					ArrayList<String> record = new ArrayList<String>();

					for (int j = 0; j < row.length; j++) {
						record.add(row[j]);
					}

					/*** Write the record to file ***/
					if (record.size() > 0) {
						String[] newArray = new String[record.size()];
						writer.writeNext(record.toArray(newArray));
					}
				}

				// Close
				reader.close();
				fr.close();

				// close the writer
				writer.flushQuietly();
				writer.close();
				fw.close();
			}

			// cleanup
			newCSVFile = FileUtil.replaceFile(csvFile, newCSVFile);
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("filterNonHeaderRows exception! csvFile=" + csvPath + ", headerKeys=" + headerKeys.toString(), e);
			Logger.getGmoLogger().printError("Error filtering non-header rows from " + csvPath + "!");
		}
		return newCSVFile;
	}

	/**
	 * Merge CSV files by appending rows. Must have same column data structure (i.e. same columns)
	 * Will include additional column "Filename" to keep track of where data came from.
	 * 
	 * @param csvFile - CSV file
	 * @return File with non-header rows filtered out
	 */
	public static File mergeTxtFilesAppendRows(String inputDirPath, String regexFilesMerge, String mergedOutputFile)
	{
		File newCSVFile = null;
		boolean headerLineDone = false;
		try {
			File inputDir = new File(inputDirPath);
			if (inputDir == null || !inputDir.isDirectory()) {
				return newCSVFile;
			}

			newCSVFile = new File(FileUtil.getCmCiqDirectory() + File.separator + mergedOutputFile + ".csv");
			Files.deleteIfExists(newCSVFile.toPath());
			FileWriter fw = new FileWriter(newCSVFile.getPath());
			CSVWriter writer = new CSVWriter(fw);

			List<String> headerRows = new ArrayList<String>();

			for (File file : inputDir.listFiles()) {
				int rowCounter = 0;
				if (StringUtil.doesMatch(file.getName(), ".+\\.txt", Pattern.CASE_INSENSITIVE) && StringUtil.doesMatch(file.getName(), regexFilesMerge, Pattern.CASE_INSENSITIVE)) {
					try (BufferedReader br = new BufferedReader(new FileReader(file))) {
						String line;
						while ((line = br.readLine()) != null) {
														
							/*** skip empty rows ***/
							boolean rowHasData = false;
							for (String cell : line.split("\\s")) {
								if (!cell.isEmpty()) {
									rowHasData = true;
								}
							}
							if (!rowHasData) {
								continue;
							}

							/*** algorithm to skip additional headers ***/
							boolean writeRowData = true;
							if (rowCounter++ < 1) {
								for (String headerRow : headerRows) {
									if (headerRow.equals(line)) {
										writeRowData = false;
									}
								}
								headerRows.add(line);
							}

							if (writeRowData) {
								/*** Create record ***/
								ArrayList<String> record = new ArrayList<String>();

								for (int j = 0; j < line.split("\\s").length; j++) {
									record.add(line.split("\\s")[j]);
								}

								// include Filename data
								if (!headerLineDone) {
									record.add("Filename");
									headerLineDone = true;
								}
								else {
									record.add(file.getName());
								}

								/*** Write the record to file ***/
								if (record.size() > 0) {
									String[] newArray = new String[record.size()];
									writer.writeNext(record.toArray(newArray));
								}
							}
						}
					}
					catch (Exception e) {
						Logger.logger.error("Error handling " + file.getPath() + "!", e);
						Logger.getGmoLogger().printError("Error handling " + file.getPath() + "!");
					}
				}
			}

			// close
			writer.flushQuietly();
			writer.close();
			fw.close();
		}
		catch (Exception e) {
			Logger.logger.error("mergeTxtFilesAppendRows exception! inputDirPath=" + inputDirPath + ", regexFilesMerge=" + regexFilesMerge, e);
			Logger.getGmoLogger().printError("Error merging " + regexFilesMerge + " files! Please check " + inputDirPath + ".");
		}
		return newCSVFile;
	}

	private void populateMOCToKgetCsvFile(File kgetExtractFile, List<String> mocListForCSVLogic)
	{
		try {
			for (String moc : mocListForCSVLogic) {
				File kgetFile = kgetExtractFile;
				if (kgetExtractFile.isDirectory()) {
					kgetFile = new File(kgetExtractFile.getPath() + File.separator + "ParsedKgetData_" + moc + ".xls");
				}

				if (moc.equals("EUtranCellFDD") || moc.equals("EUtranCellTDD")) {
					File file1 = convertCIQToCSV(kgetFile, moc + "~", "KGET_" + moc.toUpperCase());
					File file2 = convertCIQToCSV(kgetFile, moc + "1~", "KGET_" + moc.toUpperCase() + "1");
					if (file2 != null && !file2.getPath().isEmpty()) {
						File mergedFile = mergeCSVFilesAppendColumns(new File[] { file1, file2 }, "KGET_" + moc.toUpperCase() + "_Merged");
						mocToKgetCsvFile.put(moc, mergedFile);
					}
					else {
						mocToKgetCsvFile.put(moc, convertCIQToCSV(kgetFile, moc + "~", "KGET_" + moc.toUpperCase()));
					}
				}
				else {
					mocToKgetCsvFile.put(moc, convertCIQToCSV(kgetFile, moc + "~", "KGET_" + moc.toUpperCase()));
				}
			}
		}
		catch (Exception e) {
			logger.error("populateMOCToKgetCsvFile exception!", e);
			gmoLogger.printError("Populate MOC to KGET CSV file exception! " + e.getMessage());
		}
	}

	/**
	 * Read all data from G2 MIM CSV
	 * @param softwareLevel
	 * @return
	 */
	public static HashSet<String> readAllDataFromG2MIMCSV(String softwareLevel)
	{
		HashSet<String> mimData = new HashSet<String>();
		try {
			// File g1MimFile = new File(FileUtil.getCmCiqDirectory() + File.separator + "Parsed_Mim_G1_" + softwareLevel + ".csv");
			File g2MimFile = new File(FileUtil.getCmCiqDirectory() + File.separator + "Parsed_Mim_G2_" + softwareLevel + ".csv");

			// Build reader instance
			FileReader fr = new FileReader(g2MimFile);
			CSVReader reader = constructCSVReader(fr, 1);

			// Read all rows at once
			List<String[]> allRows = reader.readAll();

			/**
			 * Read CSV line by line and use the string array as you want
			 * row[0] = CLASS_NAME
			 * row[10] = ATTR_NAME
			 * row[27] = ATTR_VISIBILITY
			 */
			for (String[] row : allRows) {
				mimData.add(row[0] + "." + row[10]);
			}

			// Close
			reader.close();
			fr.close();
		}
		catch (Exception e) {
			Logger.logger.error("readAllDataFromG2MIMCSV exception! softwareLevel=" + softwareLevel, e);
			Logger.getGmoLogger().printError("Error reading data from " + softwareLevel + " G2 MIM CSV!");
		}
		return mimData;
	}

	public static HashMap<String, String> readDataFromRadioPIUTypeCSV()
	{
		HashMap<String, String> radioBandToPIUType = new HashMap<String, String>();
		try {
			File radioPIUTypeCSV = new File(FileUtil.getCmCiqDirectory() + File.separator + "RADIO_PIUTYPE.csv");

			if (radioPIUTypeCSV.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(radioPIUTypeCSV);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/**
				 * Read CSV line by line and use the string array as you want
				 * row[0] = ProductName
				 * row[1] = ProdNo
				 */
				for (String[] row : allRows) {
					String key = row[0].toUpperCase().replaceAll("[\\s]", "");
					if (StringUtil.doesMatch(row[0], "AIR.*", Pattern.CASE_INSENSITIVE)) {
						key = row[0].split("\\s")[0] + row[0].split("\\s")[1] + row[0].split("\\s")[2].replaceAll("/.*", "").replaceAll("[\\D]+$", "");
					}
					else if (StringUtil.doesMatch(row[0], "RUS.*", Pattern.CASE_INSENSITIVE)) {
						key = row[0].split("\\s")[0] + row[0].split("\\s")[2];
					}
					else if (StringUtil.doesMatch(row[0], "mRRUS.*", Pattern.CASE_INSENSITIVE)) {
						key = row[0].split("\\s")[0].toUpperCase() + row[0].split("\\s")[2];
					}
					else if (StringUtil.doesMatch(row[0], "Radio (0208|2012|2203|2212|2217|2218|2219|2237|4412).*", Pattern.CASE_INSENSITIVE)) {
						key = row[0].split("\\s")[1] + row[0].split("\\s")[2];
					}
					radioBandToPIUType.put(key, row[1].replaceAll("\\s", ""));
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("readDataFromRadioPIUTypeCSV exception!", e);
			Logger.getGmoLogger().printError("Error reading data from RADIO_PIUTYPE.csv!");
		}
		return radioBandToPIUType;
	}

	/**
	 * Reads a data row from CSV file with data that matches a regular expression.
	 * 
	 * @param csvFile - CSV file
	 * @param lookupValue - regex value to match
	 * @return String of all data in row delimited by ;
	 */
	public static String readDataRowFromCSVFile(File csvFile, String lookupValue)
	{
		String dataRowStr = "";
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				for (String[] row : allRows) {
					if (StringUtil.doesMatch(Arrays.asList(row).toString(), lookupValue, Pattern.CASE_INSENSITIVE)) {
						dataRowStr = String.join(";", row);
						break;
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowFromCSVFile exception! csvFile=" + csvPath + ", lookupValue=" + lookupValue, e);
			Logger.getGmoLogger().printError("Error reading data row from " + csvPath + "!");
		}
		return dataRowStr;
	}

	/**
	 * Reads a data row from CSV file using 1 column as reference.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column 
	 * @param lookupValue1 - value to match under 1st reference column
	 * @return single HashMap where key is column name and value is value under that column
	 */
	public static HashMap<String, String> readDataRowFromCSVFile(File csvFile, String refCol1, String lookupValue1)
	{
		HashMap<String, String> dataRow = new HashMap<String, String>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							if (!row[j].isEmpty()) {
								colNumToHeader.put(j, row[j]);
							}
						}
						else {
							if (colNumToHeader.get(j) != null && !colNumToHeader.get(j).isEmpty()) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						dataRow = headerToValueMap;
						break;
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1, e);
			Logger.getGmoLogger().printError("Error reading data row from " + csvPath + "!");
		}
		return dataRow;
	}
	
	/**
	 * Reads a data row from CSV file using 1 column as reference.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column 
	 * @param lookupValue1 - value to match under 1st reference column
	 * @return single HashMap where key is column name and value is value under that column
	 */
	public static HashMap<String, String> readDataRowFromCSVFileIgnoreSpaces(File csvFile, String refCol1, String lookupValue1)
	{
		HashMap<String, String> dataRow = new HashMap<String, String>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (!headerProcessed) {
							
							String header = row[j].replaceAll("\u00A0", "");
							if (StringUtil.doesMatch(header, refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							/*** store header column index to map ***/

							if (!header.isEmpty()) {
								colNumToHeader.put(j, header);
							}
						
						}
						else {
							if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							
							if (colNumToHeader.get(j) != null && !colNumToHeader.get(j).isEmpty()) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
							
						}

						
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						dataRow = headerToValueMap;
						break;
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1, e);
			Logger.getGmoLogger().printError("Error reading data row from " + csvPath + "!");
		}
		return dataRow;
	}

	/**
	 * Reads a data row from CSV file using 2 columns as reference.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column 
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @return single HashMap where key is column name and value is value under that column
	 */
	public static HashMap<String, String> readDataRowFromCSVFile(File csvFile, String refCol1, String lookupValue1, String refCol2, String lookupValue2)
	{
		HashMap<String, String> dataRow = new HashMap<String, String>();
		try {
			if (csvFile != null && csvFile.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
							refCol2Index = j;
						}						

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
							dataRow = headerToValueMap;
							break;
						}
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2, e);
			Logger.getGmoLogger().printError("Error reading data row from " + csvPath + "!");
		}
		return dataRow;
	}
	
	/**
	 * Reads a data row from CSV file using 2 columns as reference.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column 
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @return single HashMap where key is column name and value is value under that column
	 */
	public static HashMap<String, String> readDataRowFromCSVFileIgnoreSpaces(File csvFile, String refCol1, String lookupValue1, String refCol2, String lookupValue2)
	{
		HashMap<String, String> dataRow = new HashMap<String, String>();
		try {
			if (csvFile != null && csvFile.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {						
						if (!headerProcessed) {
							String header = row[j].replaceAll("\u00A0", "");
							if (StringUtil.doesMatch(header, refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							if (StringUtil.doesMatch(header, refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
								refCol2Index = j;
							}
							
							colNumToHeader.put(j, header);

							
						}
						else {
							
							if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
								refCol2Index = j;
							}
							
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
							
						}
						
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
							dataRow = headerToValueMap;
							break;
						}
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2, e);
			Logger.getGmoLogger().printError("Error reading data row from " + csvPath + "!");
		}
		return dataRow;
	}

	/**
	 * Reads a data row from CSV file using 3 columns as reference.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1/2/3 - 1st/2nd/3rd reference column 
	 * @param lookupValue1/2/3 - value to match under 1st/2nd/3rd reference column
	 * @return single HashMap where key is column name and value is value under that column
	 */
	public static HashMap<String, String> readDataRowFromCSVFile(File csvFile, String refCol1, String lookupValue1, String refCol2, String lookupValue2, String refCol3, String lookupValue3)
	{
		HashMap<String, String> dataRow = new HashMap<String, String>();
		try {
			if (csvFile != null && csvFile.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				int refCol3Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
							refCol2Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol3, Pattern.CASE_INSENSITIVE) && refCol3Index < 0) {
							refCol3Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";
					String refVal3 = refCol3Index > -1 ? row[refCol3Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
							if (!refVal3.isEmpty() && StringUtil.doesMatch(refVal3, lookupValue3, Pattern.CASE_INSENSITIVE)) {
								dataRow = headerToValueMap;
								break;
							}
						}
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			logger.error("readDataRowFromCSVFile exception!", e);
			gmoLogger.printError("Read data row from CSV file exception! " + e.getMessage());
		}
		return dataRow;
	}

	/**
	 * Reads a data row from CSV file using 4 columns as reference.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1/2/3/4 - 1st/2nd/3rd/4th reference column 
	 * @param lookupValue1/2/3/4 - value to match under 1st/2nd/3rd/4th reference column
	 * @return single HashMap where key is column name and value is value under that column
	 */
	public static HashMap<String, String> readDataRowFromCSVFile(File csvFile, String refCol1, String lookupValue1, String refCol2, String lookupValue2, String refCol3, String lookupValue3, String refCol4, String lookupValue4)
	{
		HashMap<String, String> dataRow = new HashMap<String, String>();
		try {
			if (csvFile != null && csvFile.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				int refCol3Index = -1;
				int refCol4Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
							refCol2Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol3, Pattern.CASE_INSENSITIVE) && refCol3Index < 0) {
							refCol3Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol4, Pattern.CASE_INSENSITIVE) && refCol4Index < 0) {
							refCol4Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";
					String refVal3 = refCol3Index > -1 ? row[refCol3Index] : "";
					String refVal4 = refCol4Index > -1 ? row[refCol4Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
							if (!refVal3.isEmpty() && StringUtil.doesMatch(refVal3, lookupValue3, Pattern.CASE_INSENSITIVE)) {
								if (!refVal4.isEmpty() && StringUtil.doesMatch(refVal4, lookupValue4, Pattern.CASE_INSENSITIVE)) {
									dataRow = headerToValueMap;
									break;
								}
							}
						}
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2 + ", refCol3=" + refCol3 + ", lookupValue3=" + lookupValue3 + ", refCol4=" + refCol4 + ", lookupValue4=" + lookupValue4, e);
			Logger.getGmoLogger().printError("Error reading data row from " + csvPath + "!");
		}
		return dataRow;
	}

	/**
	 * Reads a data row from CSV file using 5 columns as reference.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1/2/3/4/5 - 1st/2nd/3rd/4th reference column 
	 * @param lookupValue1/2/3/4/g - value to match under 1st/2nd/3rd/4th reference column
	 * @return single HashMap where key is column name and value is value under that column
	 */
	public static HashMap<String, String> readDataRowFromCSVFile(File csvFile, String refCol1, String lookupValue1, String refCol2, String lookupValue2, String refCol3, String lookupValue3, String refCol4, String lookupValue4, String refCol5, String lookupValue5)
	{
		HashMap<String, String> dataRow = new HashMap<String, String>();
		try {
			if (csvFile != null && csvFile.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				int refCol3Index = -1;
				int refCol4Index = -1;
				int refCol5Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
							refCol2Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol3, Pattern.CASE_INSENSITIVE) && refCol3Index < 0) {
							refCol3Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol4, Pattern.CASE_INSENSITIVE) && refCol4Index < 0) {
							refCol4Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol5, Pattern.CASE_INSENSITIVE) && refCol5Index < 0) {
							refCol5Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";
					String refVal3 = refCol3Index > -1 ? row[refCol3Index] : "";
					String refVal4 = refCol4Index > -1 ? row[refCol4Index] : "";
					String refVal5 = refCol5Index > -1 ? row[refCol5Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
							if (!refVal3.isEmpty() && StringUtil.doesMatch(refVal3, lookupValue3, Pattern.CASE_INSENSITIVE)) {
								if (!refVal4.isEmpty() && StringUtil.doesMatch(refVal4, lookupValue4, Pattern.CASE_INSENSITIVE)) {
									if (!refVal5.isEmpty() && StringUtil.doesMatch(refVal5, lookupValue5, Pattern.CASE_INSENSITIVE)) {
										dataRow = headerToValueMap;
										break;
									}
								}
							}
						}
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2 + ", refCol3=" + refCol3 + ", lookupValue3=" + lookupValue3 + ", refCol4=" + refCol4 + ", lookupValue4=" + lookupValue4 + ", refCol5=" + refCol5 + ", lookupValue5=" + lookupValue5, e);
			Logger.getGmoLogger().printError("Error reading data row from " + csvPath + "!");
		}
		return dataRow;
	}

	/**
	 * Return an array of data rows that matches a value under a reference column.
	 * Missing column headers will be added using previous column header as reference.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayFromCSVFileWithMissingHeaders(File csvFile, String refCol1, String lookupValue1)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				String previousHeader = "";
				int counter = 1;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							if (!row[j].isEmpty()) {
								colNumToHeader.put(j, row[j]);
								previousHeader = row[j];
								counter = 1;
							}
							else {
								previousHeader += "." + counter++;
								colNumToHeader.put(j, previousHeader);
							}
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						dataRowArray.add(headerToValueMap);
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayFromCSVFileWithMissingHeaders exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1, e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}

	/**
	 * Return an array of data rows that matches a value under a reference column.
	 * Missing column headers will be added using previous column header as reference.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayFromCSVFileWithMissingHeadersAddingColumn(File csvFile, String refCol1, String lookupValue1)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				String previousHeader = "";
				int counter = 1;
				List<String> headers =  new ArrayList<>();
				
				headers.addAll(Arrays.asList(allRows.get(0)));
				headers.add(headers.size(), "");
				String[] stringArray = headers.toArray(new String[0]);
				allRows.add(0,stringArray);
				
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							if (!row[j].isEmpty()) {
								colNumToHeader.put(j, row[j]);
								previousHeader = row[j];
								counter = 1;
							}
							else {
								previousHeader += "." + counter++;
								colNumToHeader.put(j, previousHeader);
							}
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						dataRowArray.add(headerToValueMap);
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayFromCSVFileWithMissingHeaders exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1, e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}
	
	/**
	 * Return an array of data rows that matches a value under a reference column.
	 * Column headers from multiple rows (top-down) will be merged together.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayFromCSVFileWithMultipleHeaders(File csvFile, String refCol1, String lookupValue1, int numOfHeaderRows)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				// process header rows
				Map<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				List<String[]> headerRows = new ArrayList<String[]>();
				int maxHeaderRowLength = 0;
				// calculate headerRows
				for (int i = 0; i < numOfHeaderRows; i++) {
					// get max row length from all header rows
					if (allRows.size() >= (i + 1)) {
						maxHeaderRowLength = allRows.get(i).length > maxHeaderRowLength ? allRows.get(i).length : maxHeaderRowLength;
						headerRows.add(allRows.get(i));
					}
				}
				for (int i = 0; i < maxHeaderRowLength; i++) {
					String headerName = "";
					for (String[] row : headerRows) {
						headerName += row[i];
					}
					colNumToHeader.put(i, headerName);
				}

				/*** initialize column index ***/
				int refCol1Index = -1;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (colNumToHeader.get(j) != null) {
							headerToValueMap.put(colNumToHeader.get(j), row[j]);
						}
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						dataRowArray.add(headerToValueMap);
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayFromCSVFileWithMultipleHeaders exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", numOfHeaderRows=" + numOfHeaderRows, e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}

	/**
	 * Return an array of data rows that matches a value under a reference column.
	 * 
	 * @param file - tab delimited file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayFromTabDelimitedFile(File file, String refCol1, String lookupValue1)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (file != null && file.exists()) {

				/*** initialize column index ***/
				int refCol1Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				String line;
				FileReader fr = new FileReader(file);
				BufferedReader br = new BufferedReader(fr);

				while ((line = br.readLine()) != null) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < line.split("\t").length; j++) {
						if (StringUtil.doesMatch(line.split("\t")[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, line.split("\t")[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), line.split("\t")[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? line.split("\t")[refCol1Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						dataRowArray.add(headerToValueMap);
					}
				}

				// Close
				br.close();
				fr.close();
			}
		}
		catch (Exception e) {
			logger.error("readDataRowArrayFromTabDelimitedFile exception!", e);
			gmoLogger.printError("readDataRowArrayFromTabDelimitedFile exception! " + e.getMessage());
		}
		return dataRowArray;
	}

	/**
	 * Return an array of data rows that matches a value under a reference column.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayFromCSVFile(File csvFile, String refCol1, String lookupValue1)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						dataRowArray.add(headerToValueMap);
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1, e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}
	
	/**
	 * Return an array of data rows that matches a value under a reference column.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayFromCSVFileIgnoreSpaces(File csvFile, String refCol1, String lookupValue1)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (!headerProcessed) {
							String header = row[j].replaceAll("\u00A0", "");
							if (StringUtil.doesMatch(header, refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							/*** store header column index to map ***/
							colNumToHeader.put(j, header);
							
						}else {
							if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						dataRowArray.add(headerToValueMap);
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1, e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}

	/**
	 * Return an array of data rows .
	 * 
	 * @param csvFile - CSV file
	
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readAllDataRowArrayFromCSVFile(File csvFile)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						/*
						 * if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) &&
						 * refCol1Index < 0) { refCol1Index = j; }
						 */

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					//String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";

					//if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						dataRowArray.add(headerToValueMap);
					//}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayFromCSVFile exception! csvFile=" + csvPath , e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}
		
	/**
	 * Return an array of data rows that matches a value under a reference column.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayFromCSVFile(File csvFile, String refCol1, String lookupValue1, String refCol2, String lookupValue2)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
							refCol2Index = j;
						}						

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
							dataRowArray.add(headerToValueMap);
						}
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2, e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}
	
	/**
	 * Return an array of data rows that matches a value under a reference column.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayFromCSVFileIgnoreSpaces(File csvFile, String refCol1, String lookupValue1, String refCol2, String lookupValue2)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if(!headerProcessed) {
							String header = row[j].replaceAll("\u00A0", "");
							if (StringUtil.doesMatch(header, refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							if (StringUtil.doesMatch(header, refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
								refCol2Index = j;
							}
							/*** store header column index to map ***/
							colNumToHeader.put(j, header);

							
						}else {
							if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
								refCol1Index = j;
							}
							if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
								refCol2Index = j;
							}
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
							
						}						
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
							dataRowArray.add(headerToValueMap);
						}
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2, e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}
	
	/**
	 * Return an array of data rows that matches a value under a reference column.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @param refCol3 - 3rd reference column
	 * @param lookupValue3 - value to match under 3rd reference column
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayFromCSVFile(File csvFile, String refCol1, String lookupValue1, String refCol2, String lookupValue2, String refCol3, String lookupValue3)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				int refCol3Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
							refCol2Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol3, Pattern.CASE_INSENSITIVE) && refCol3Index < 0) {
							refCol3Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";
					String refVal3 = refCol3Index > -1 ? row[refCol3Index] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						if (!refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
							if (!refVal3.isEmpty() && StringUtil.doesMatch(refVal3, lookupValue3, Pattern.CASE_INSENSITIVE)) {
								dataRowArray.add(headerToValueMap);
							}
						}
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2 + ", refCol3=" + refCol3 + ", lookupValue3=" + lookupValue3, e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}

	/**
	 * Return an array of data rows that matches all values under a reference column.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - values to match under 1st reference column, delimited by ","
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayThatMatchAllValues(File csvFile, String refCol1, List<String> lookupValues1)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";

					if (!refVal1.isEmpty()) {
						// init as true, check that lookupValues1 all need to match
						boolean lookupValues1Match = true;
						for (String lookupValue1 : lookupValues1) {
							// skip empty values
							if (lookupValue1.trim().isEmpty()) {
								continue;
							}
							// init as false, check that just one of the refVal1 need to match
							boolean refVal1Match = false;
							for (String refVal : refVal1.split(",")) {
								// skip empty values
								if (refVal.trim().isEmpty()) {
									continue;
								}
								// if one of the refVal1 match then refVal1Match condition is satisfied, break loop
								if (StringUtil.doesMatch(refVal.toLowerCase().replaceAll("[\\s_-]", ""), ".*" + lookupValue1.toLowerCase().replaceAll("[\\s_-]", "") + ".*", Pattern.CASE_INSENSITIVE)) {
									refVal1Match = true;
									break;
								}
							}
							// if none of the refVal1 match then lookupValues1Match condition is not satisfied, break loop
							if (!refVal1Match) {
								lookupValues1Match = false;
								break;
							}
						}
						// if 1st condition passes, then include data row
						if (lookupValues1Match) {
							dataRowArray.add(headerToValueMap);
						}
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayThatMatchAllValues exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValues1=" + lookupValues1.toString(), e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}

	/**
	 * Return an array of data rows that matches all values under a reference column.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - values to match under 1st reference column, delimited by ","
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - values to match under 2nd reference column, delimited by ","
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayThatMatchAllValues(File csvFile, String refCol1, List<String> lookupValues1, String refCol2, List<String> lookupValues2)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
							refCol2Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";

					if (!refVal1.isEmpty()) {
						// init as true, check that lookupValues1 all need to match
						boolean lookupValues1Match = true;
						for (String lookupValue1 : lookupValues1) {
							// skip empty values
							if (lookupValue1.trim().isEmpty()) {
								continue;
							}
							// init as false, check that just one of the refVal1 need to match
							boolean refVal1Match = false;
							for (String refVal : refVal1.split(",")) {
								// skip empty values
								if (refVal.trim().isEmpty()) {
									continue;
								}
								// if one of the refVal1 match then refVal1Match condition is satisfied, break loop
								if (StringUtil.doesMatch(refVal.toLowerCase().replaceAll("[\\s_-]", ""), ".*" + lookupValue1.toLowerCase().replaceAll("[\\s_-]", "") + ".*", Pattern.CASE_INSENSITIVE)) {
									refVal1Match = true;
									break;
								}
							}
							// if none of the refVal1 match then lookupValues1Match condition is not satisfied, break loop
							if (!refVal1Match) {
								lookupValues1Match = false;
								break;
							}
						}
						// if 1st condition passes, proceed to 2nd condition
						if (lookupValues1Match) {
							// init as true, check that lookupValues2 all need to match
							boolean lookupValues2Match = true;
							for (String lookupValue2 : lookupValues2) {
								// skip empty values
								if (lookupValue2.trim().isEmpty()) {
									continue;
								}
								// init as false, check that just one of the refVal2 need to match
								boolean refVal2Match = false;
								for (String refVal : refVal2.split(",")) {
									// skip empty values
									if (refVal.trim().isEmpty()) {
										continue;
									}
									// if one of the refVal2 match then refVal2Match condition is satisfied, break loop
									if (StringUtil.doesMatch(refVal.toLowerCase().replaceAll("[\\s_-]", ""), ".*" + lookupValue2.toLowerCase().replaceAll("[\\s_-]", "") + ".*", Pattern.CASE_INSENSITIVE)) {
										refVal2Match = true;
										break;
									}
								}
								// if none of the refVal2 match then lookupValues2Match condition is not satisfied, break loop
								if (!refVal2Match) {
									lookupValues2Match = false;
									break;
								}
							}
							// if 2nd condition also passes, then include data row
							if (lookupValues2Match) {
								dataRowArray.add(headerToValueMap);
							}
						}
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayThatMatchAllValues exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValues1=" + lookupValues1.toString() + ", refCol2=" + refCol2 + ", lookupValues2=" + lookupValues2.toString(), e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}

	/**
	 * Return an array of data rows that match any one value under a reference column.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - values to match under 1st reference column, delimited by ","
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayThatMatchOneValue(File csvFile, String refCol1, List<String> lookupValues1)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";

					if (!refVal1.isEmpty()) {
						// init as false, check that just one of the lookupValues1 need to match
						boolean lookupValues1Match = false;
						for (String lookupValue1 : lookupValues1) {
							// skip empty values
							if (lookupValue1.trim().isEmpty()) {
								continue;
							}
							// init as false, check that just one of the refVal1 need to match
							boolean refVal1Match = false;
							for (String refVal : refVal1.split(",")) {
								// skip empty values
								if (refVal.trim().isEmpty()) {
									continue;
								}
								// if one of the refVal1 match then refVal1Match condition is satisfied, break loop
								if (StringUtil.doesMatch(refVal.toLowerCase().replaceAll("[\\s_-]", ""), ".*" + lookupValue1.toLowerCase().replaceAll("[\\s_-]", "") + ".*", Pattern.CASE_INSENSITIVE)) {
									refVal1Match = true;
									break;
								}
							}
							// if none of the refVal1 match then lookupValues1Match condition is not satisfied, break loop
							if (refVal1Match) {
								lookupValues1Match = true;
								break;
							}
						}
						// if 1st condition passes, then include data row
						if (lookupValues1Match) {
							dataRowArray.add(headerToValueMap);
						}
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayThatMatchOneValue exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValues1=" + lookupValues1.toString(), e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}
	
	/**
	 * Return an array of data rows that match any one value under a reference column.
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - values to match under 1st reference column, delimited by ","
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - values to match under 2nd reference column, delimited by ","
	 * @return ArrayList of HashMaps where each HashMap contains key=column name and value=column value
	 */
	public static ArrayList<HashMap<String, String>> readDataRowArrayThatMatchOneValue(File csvFile, String refCol1, List<String> lookupValues1, String refCol2, List<String> lookupValues2)
	{
		ArrayList<HashMap<String, String>> dataRowArray = new ArrayList<HashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					HashMap<String, String> headerToValueMap = new HashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
							refCol2Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";

					// init as false, check that just one of the lookupValues1 need to match
					boolean lookupValues1Match = false;
					if (!refVal1.isEmpty()) {
						for (String lookupValue1 : lookupValues1) {
							// skip empty values
							if (lookupValue1.trim().isEmpty()) {
								continue;
							}
							// init as false, check that just one of the refVal1 need to match
							boolean refVal1Match = false;
							for (String refVal : refVal1.split(",")) {
								// skip empty values
								if (refVal.trim().isEmpty()) {
									continue;
								}
								// if one of the refVal1 match then refVal1Match condition is satisfied, break loop
								if (StringUtil.doesMatch(refVal.toLowerCase().replaceAll("[\\s_-]", ""), lookupValue1.toLowerCase().replaceAll("[\\s_-]", ""), Pattern.CASE_INSENSITIVE)) {
									refVal1Match = true;
									break;
								}
							}
							// if none of the refVal1 match then lookupValues1Match condition is not satisfied, break loop
							if (refVal1Match) {
								lookupValues1Match = true;
								break;
							}
						}
					}

					// init as false, check that just one of the lookupValues2 need to match
					boolean lookupValues2Match = false;
					if (!refVal2.isEmpty()) {
						for (String lookupValue2 : lookupValues2) {
							// skip empty values
							if (lookupValue2.trim().isEmpty()) {
								continue;
							}
							// init as false, check that just one of the refVal2 need to match
							boolean refVal2Match = false;
							for (String refVal : refVal2.split(",")) {
								// skip empty values
								if (refVal.trim().isEmpty()) {
									continue;
								}
								// if one of the refVal2 match then refVal2Match condition is satisfied, break loop
								if (StringUtil.doesMatch(refVal.toLowerCase().replaceAll("[\\s_-]", ""), lookupValue2.toLowerCase().replaceAll("[\\s_-]", ""), Pattern.CASE_INSENSITIVE)) {
									refVal2Match = true;
									break;
								}
							}
							// if none of the refVal2 match then lookupValues2Match condition is not satisfied, break loop
							if (refVal2Match) {
								lookupValues2Match = true;
								break;
							}
						}

					}

					// if 1st and 2nd conditions pass, then include data row
					if (lookupValues1Match && lookupValues2Match) {
						dataRowArray.add(headerToValueMap);
					}

				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataRowArrayThatMatchOneValue exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValues1=" + lookupValues1.toString() + ", refCol2=" + refCol2 + ", lookupValues2=" + lookupValues2.toString(), e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}

	/**
	 * Return an array of data rows by preserving the order of data that match any one value under a reference column.
	 * @param csvFile
	 * @param refCol1
	 * @param lookupValues1
	 * @return
	 */
	public static LinkedList<LinkedHashMap<String, String>> readOrderedDataRowArrayThatMatchOneValue(File csvFile, String refCol1, List<String> lookupValues1)
	{
		LinkedList<LinkedHashMap<String, String>> dataRowArray = new LinkedList<LinkedHashMap<String, String>>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				HashMap<Integer, String> colNumToHeader = new HashMap<Integer, String>();
				boolean headerProcessed = false;
				for (String[] row : allRows) {
					LinkedHashMap<String, String> headerToValueMap = new LinkedHashMap<String, String>();
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}

						/*** store header column index to map ***/
						if (!headerProcessed) {
							colNumToHeader.put(j, row[j]);
						}
						else {
							if (colNumToHeader.get(j) != null) {
								headerToValueMap.put(colNumToHeader.get(j), row[j]);
							}
						}
					}

					/*** set flag and go to next data row ***/
					if (!headerProcessed) {
						headerProcessed = true;
						continue;
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					if (!refVal1.isEmpty()) {
						// init as false, check that just one of the lookupValues1 need to match
						boolean lookupValues1Match = false;
						for (String lookupValue1 : lookupValues1) {
							// skip empty values
							if (lookupValue1.trim().isEmpty()) {
								continue;
							}
							// init as false, check that just one of the refVal1 need to match
							boolean refVal1Match = false;
							for (String refVal : refVal1.split(",")) {
								// skip empty values
								if (refVal.trim().isEmpty()) {
									continue;
								}
								// if one of the refVal1 match then refVal1Match condition is satisfied, break loop
								if (StringUtil.doesMatch(refVal.toLowerCase().replaceAll("[\\s_-]", ""), ".*" + lookupValue1.toLowerCase().replaceAll("[\\s_-]", "") + ".*", Pattern.CASE_INSENSITIVE)) {
									refVal1Match = true;
									break;
								}
							}
							// if none of the refVal1 match then lookupValues1Match condition is not satisfied, break loop
							if (refVal1Match) {
								lookupValues1Match = true;
								break;
							}
						}
						// if 1st condition passes, then include data row
						if (lookupValues1Match) {
							dataRowArray.add(headerToValueMap);
						}
					}
				}
				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readOrderedDataRowArrayThatMatchOneValue exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValues1=" + lookupValues1.toString(), e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataRowArray;
	}

	/**
	 * Returns values under dataColumn in rows that matched lookupValue1 under refCol1
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param dataColumn - column to pull the data from
	 * @param resultsToUpperCase - if true results are converted to uppercase. if false results are left as is
	 * @return ArrayList of values under dataColumn in rows that matched lookupValue1 under refCol1
	 */
	public static ArrayList<String> readDataArrayFromCSVFile(File csvFile, String refCol1, String lookupValue1, String dataColumn, boolean resultsToUpperCase)
	{
		ArrayList<String> dataArray = new ArrayList<String>();
		try {
			if (csvFile != null && csvFile.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int dataColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (StringUtil.doesMatch(row[j], dataColumn, Pattern.CASE_INSENSITIVE) && dataColIndex < 0) {
							dataColIndex = j;
						}
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String dataValue = dataColIndex > -1 ? row[dataColIndex] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						dataArray.add(resultsToUpperCase ? dataValue.trim().toUpperCase() : dataValue.trim());
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataArrayFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", dataColumn=" + dataColumn, e);
			Logger.getGmoLogger().printError("Error reading data row array from " + csvPath + "!");
		}
		return dataArray;
	}

	/**
	 * Return values under dataColumn in rows that matched refCol1/lookupValue1 and refCol2/lookupValue2 
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @param dataColumn - column to pull the data from
	 * @param resultsToUpperCase - if true results are converted to uppercase. if false results are left as is
	 * @return ArrayList of values under dataColumn in rows that matched refCol1/lookupValue1 and refCol2/lookupValue2
	 */
	public static ArrayList<String> readDataArrayFromCSVFile(File csvFile, String refCol1, String lookupValue1, String refCol2, String lookupValue2, String dataColumn, boolean resultsToUpperCase)
	{
		ArrayList<String> dataArray = new ArrayList<String>();
		try {
			if (csvFile != null && csvFile.exists()) {
				// Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				// Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				int dataColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE) && refCol1Index < 0) {
							refCol1Index = j;
						}
						if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE) && refCol2Index < 0) {
							refCol2Index = j;
						}
						if (StringUtil.doesMatch(row[j], dataColumn, Pattern.CASE_INSENSITIVE) && dataColIndex < 0) {
							dataColIndex = j;
						}
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : null;
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : null;
					String dataValue = dataColIndex > -1 ? row[dataColIndex] : "";

					if (refVal1 != null && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						if (refVal2 != null && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
							dataArray.add(resultsToUpperCase ? dataValue.trim().toUpperCase() : dataValue.trim());
						}
					}
				}

				// Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataArrayFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2 + ", dataColumn=" + dataColumn, e);
			Logger.getGmoLogger().printError("Error reading data array from " + csvPath + "!");
		}
		return dataArray;
	}

	/**
	 * Read data from a cell in CSV File in row that matched lookupValue1 under refCol1
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param dataColumn - column to pull the data from
	 * @return String of value in cell
	 */
	public static String readDataFromCSVFile(File csvFile, String refCol1, String lookupValue1, String dataColumn)
	{
		String data = "";
		try {
			if (csvFile != null && csvFile.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int dataColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE)) {
							refCol1Index = refCol1Index < 0 ? j : refCol1Index;
						}
						if (StringUtil.doesMatch(row[j], dataColumn, Pattern.CASE_INSENSITIVE)) {
							dataColIndex = dataColIndex < 0 ? j : dataColIndex;
						}
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String dataValue = dataColIndex > -1 ? row[dataColIndex] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE)) {
						data = dataValue;
						break;
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", dataColumn=" + dataColumn, e);
			Logger.getGmoLogger().printError("Error reading data from " + csvPath + "!");
		}
		return data;
	}

	/**
	 * Read data from a cell in CSV File in row that matched refCol1/lookupValue1 and refCol2/lookupValue2 
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @param dataColumn - column to pull the data from
	 * @return String of value in cell
	 */
	public static String readDataFromCSVFile(File csvFile, String refCol1, String lookupValue1, String refCol2, String lookupValue2, String dataColumn)
	{
		String data = "";
		try {
			if (csvFile != null && csvFile.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				int dataColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE)) {
							refCol1Index = refCol1Index < 0 ? j : refCol1Index;
						}
						if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE)) {
							refCol2Index = refCol2Index < 0 ? j : refCol2Index;
						}
						if (StringUtil.doesMatch(row[j], dataColumn, Pattern.CASE_INSENSITIVE)) {
							dataColIndex = dataColIndex < 0 ? j : dataColIndex;
						}
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";
					String dataValue = dataColIndex > -1 ? row[dataColIndex] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE) && !refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE)) {
						data = dataValue;
						break;
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2 + ", dataColumn=" + dataColumn, e);
			Logger.getGmoLogger().printError("Error reading data from " + csvPath + "!");
		}
		return data;
	}

	/**
	 * Read data from a cell in CSV File in row that matched refCol1/lookupValue1, refCol2/lookupValue2, refCol3/lookupValue3
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param lookupValue1 - value to match under 1st reference column
	 * @param refCol2 - 2nd reference column
	 * @param lookupValue2 - value to match under 2nd reference column
	 * @param refCol3 - 3rd reference column
	 * @param lookupValue3 - value to match under 3rd reference column
	 * @param dataColumn - column to pull the data from
	 * @return String of value in cell
	 */
	public static String readDataFromCSVFile(File csvFile, String refCol1, String lookupValue1, String refCol2, String lookupValue2, String refCol3, String lookupValue3, String dataColumn)
	{
		String data = "";
		try {
			if (csvFile != null && csvFile.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int refCol2Index = -1;
				int refCol3Index = -1;
				int dataColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE)) {
							refCol1Index = refCol1Index < 0 ? j : refCol1Index;
						}
						if (StringUtil.doesMatch(row[j], refCol2, Pattern.CASE_INSENSITIVE)) {
							refCol2Index = refCol2Index < 0 ? j : refCol2Index;
						}
						if (StringUtil.doesMatch(row[j], refCol3, Pattern.CASE_INSENSITIVE)) {
							refCol3Index = refCol3Index < 0 ? j : refCol3Index;
						}
						if (StringUtil.doesMatch(row[j], dataColumn, Pattern.CASE_INSENSITIVE)) {
							dataColIndex = dataColIndex < 0 ? j : dataColIndex;
						}
					}

					String refVal1 = refCol1Index > -1 ? row[refCol1Index] : "";
					String refVal2 = refCol2Index > -1 ? row[refCol2Index] : "";
					String refVal3 = refCol3Index > -1 ? row[refCol3Index] : "";
					String dataValue = dataColIndex > -1 ? row[dataColIndex] : "";

					if (!refVal1.isEmpty() && StringUtil.doesMatch(refVal1, lookupValue1, Pattern.CASE_INSENSITIVE) && !refVal2.isEmpty() && StringUtil.doesMatch(refVal2, lookupValue2, Pattern.CASE_INSENSITIVE) && !refVal3.isEmpty() && StringUtil.doesMatch(refVal3, lookupValue3, Pattern.CASE_INSENSITIVE)) {
						data = dataValue;
						break;
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readDataFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", lookupValue1=" + lookupValue1 + ", refCol2=" + refCol2 + ", lookupValue2=" + lookupValue2 + ", refCol3=" + refCol3 + ", lookupValue3=" + lookupValue3 + ", dataColumn=" + dataColumn, e);
			Logger.getGmoLogger().printError("Error reading data from " + csvPath + "!");
		}
		return data;
	}

	/**
	 * Read column data in CSV File matched lookupValue1 under refCol1
	 * 
	 * @param csvFile - CSV file
	 * @param refCol1 - 1st reference column
	 * @param dataColumn - column to pull the data from
	 * @return String of value in cell
	 */
	public static String readColumnDataFromCSVFile(File csvFile, String refCol1, int rowOffset)
	{
		String data = "";
		try {
			if (csvFile != null && csvFile.exists()) {
				FileReader fr = new FileReader(csvFile);
				CSVReader reader = constructCSVReader(fr, 0);
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int refCol1Index = -1;
				int rowOffsetIndex = -1;
				for (int i = 0; i < allRows.size(); i++) {
					if (refCol1Index > -1 && rowOffsetIndex > -1) {
						break;
					}
					String[] row = allRows.get(i);
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], refCol1, Pattern.CASE_INSENSITIVE)) {
							refCol1Index = refCol1Index < 0 ? j : refCol1Index;
							rowOffsetIndex = i;
							break;
						}
					}
				}

				if (refCol1Index > -1 && rowOffsetIndex > -1) {
					String[] row = allRows.get(rowOffsetIndex + rowOffset);
					data = row[refCol1Index];
				}
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			String csvPath = csvFile != null ? csvFile.getPath() : "";
			Logger.logger.error("readColumnDataFromCSVFile exception! csvFile=" + csvPath + ", refCol1=" + refCol1 + ", rowOffset=" + rowOffset, e);
			Logger.getGmoLogger().printError("Error reading column data from " + csvPath + "!");
		}
		return data;
	}

	public static HashMap<String, String[]> readCellDataFromCACIQDynRnCSV()
	{
		HashMap<String, String[]> newCellToCACIQDynRnData = new HashMap<String, String[]>();
		try {
			File radioPIUTypeCSV = new File(FileUtil.getCmCiqDirectory() + File.separator + "CACIQ_DYNRN.csv");

			if (radioPIUTypeCSV.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(radioPIUTypeCSV);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int newCellColIndex = -1;
				int oldCellColIndex = -1;
				int radioNewColIndex = -1;
				int radioTypeColIndex = -1;
				int newEnbNameColIndex = -1;
				int oldEnbNameColIndex = -1;
				int includeNonMovingCellColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], "EUtranCellFDD_Old", Pattern.CASE_INSENSITIVE)) {
							oldCellColIndex = j;
						}
						else if (StringUtil.doesMatch(row[j], "EUtranCellFDD_New", Pattern.CASE_INSENSITIVE)) {
							newCellColIndex = j;
						}
						else if (StringUtil.doesMatch(row[j], "(Radio_Type_New|Radio_New)", Pattern.CASE_INSENSITIVE)) {
							radioNewColIndex = j;
						}
						else if (StringUtil.doesMatch(row[j], "New_Radio_Type", Pattern.CASE_INSENSITIVE)) {
							radioTypeColIndex = j;
						}
						else if (StringUtil.doesMatch(row[j], "eNodeB_Name_Current", Pattern.CASE_INSENSITIVE)) {
							oldEnbNameColIndex = j;
						}
						else if (StringUtil.doesMatch(row[j], "eNodeB_Name_New", Pattern.CASE_INSENSITIVE)) {
							newEnbNameColIndex = j;
						}
						else if (StringUtil.doesMatch(row[j], "Include_NonMoving_Cell", Pattern.CASE_INSENSITIVE)) {
							includeNonMovingCellColIndex = j;
						}
					}

					String oldEnbName = oldEnbNameColIndex > -1 ? row[oldEnbNameColIndex] : "";
					String oldCell = oldCellColIndex > -1 ? row[oldCellColIndex] : "";

					String newEnbName = newEnbNameColIndex > -1 ? row[newEnbNameColIndex] : "";
					String newCell = newCellColIndex > -1 ? row[newCellColIndex] : "";
					String radioNew = radioNewColIndex > -1 ? row[radioNewColIndex] : "";
					String radioType = radioTypeColIndex > -1 ? row[radioTypeColIndex] : "";
					String includeNonMovingCell = includeNonMovingCellColIndex > -1 ? row[includeNonMovingCellColIndex] : "";

					if (!newCell.isEmpty()) {
						newCellToCACIQDynRnData.put(newCell, new String[] { oldEnbName, oldCell, newEnbName, radioNew, radioType, includeNonMovingCell });
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("readCellDataFromCACIQDynRnCSV exception!", e);
			Logger.getGmoLogger().printError("Error reading cell data from CACIQ dyn RN CSV!");
		}
		return newCellToCACIQDynRnData;
	}

	public static HashMap<String, String[]> readRadioDataFromCACIQDynRnCSV()
	{
		HashMap<String, String[]> newCellRadioNewToCACIQDynRnData = new HashMap<String, String[]>();
		try {
			File radioPIUTypeCSV = new File(FileUtil.getCmCiqDirectory() + File.separator + "CACIQ_DYNRN.csv");

			if (radioPIUTypeCSV.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(radioPIUTypeCSV);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int newCellColIndex = -1;
				int oldCellColIndex = -1;
				int radioNewColIndex = -1;
				int radioTypeColIndex = -1;
				int newEnbNameColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (StringUtil.doesMatch(row[j], "EUtranCellFDD_Old", Pattern.CASE_INSENSITIVE)) {
							oldCellColIndex = j;
						}
						else if (StringUtil.doesMatch(row[j], "EUtranCellFDD_New", Pattern.CASE_INSENSITIVE)) {
							newCellColIndex = j;
						}
						else if (StringUtil.doesMatch(row[j], "(Radio_Type_New|Radio_New)", Pattern.CASE_INSENSITIVE)) {
							radioNewColIndex = j;
						}
						else if (StringUtil.doesMatch(row[j], "New_Radio_Type", Pattern.CASE_INSENSITIVE)) {
							radioTypeColIndex = j;
						}
						else if (StringUtil.doesMatch(row[j], "eNodeB_Name_New", Pattern.CASE_INSENSITIVE)) {
							newEnbNameColIndex = j;
						}
					}

					String oldCell = oldCellColIndex > -1 ? row[oldCellColIndex] : "";
					String newCell = newCellColIndex > -1 ? row[newCellColIndex] : "";
					String radioNew = radioNewColIndex > -1 ? row[radioNewColIndex] : "";
					String radioType = radioTypeColIndex > -1 ? row[radioTypeColIndex] : "";
					String newEnbName = newEnbNameColIndex > -1 ? row[newEnbNameColIndex] : "";

					if (oldCell.isEmpty() && !newCell.isEmpty()) {
						newCellRadioNewToCACIQDynRnData.put(newCell + "!" + radioNew, new String[] { oldCell, radioType, newEnbName });
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("readRadioDataFromCACIQDynRnCSV exception!", e);
			Logger.getGmoLogger().printError("Error reading readio data from CACIQ dyn RN CSV!");
		}
		return newCellRadioNewToCACIQDynRnData;
	}

	public static HashMap<String, String[]> readDataFromRNDEnbInfoCSV()
	{
		HashMap<String, String[]> newEnbNameToRNDCIQEnbInfoData = new HashMap<String, String[]>();
		try {
			File rndEnbInfoCSV = getCIQCSVFile("RNDCIQ_ENBINFO");

			if (rndEnbInfoCSV != null && rndEnbInfoCSV.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(rndEnbInfoCSV);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int enbIdColIndex = -1;
				int enbNameColIndex = -1;
				int duTypeColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (enbIdColIndex < 0 && StringUtil.doesMatch(row[j], "eNBId", Pattern.CASE_INSENSITIVE)) {
							enbIdColIndex = j;
						}
						else if (enbNameColIndex < 0 && StringUtil.doesMatch(row[j].replaceAll("\\s", ""), StringUtil.mapToRegEx("eNodeB Name"), Pattern.CASE_INSENSITIVE)) {
							enbNameColIndex = j;
						}
						else if (duTypeColIndex < 0 && StringUtil.doesMatch(row[j].replaceAll("\\s", ""), StringUtil.mapToRegEx("DU Type"), Pattern.CASE_INSENSITIVE)) {
							duTypeColIndex = j;
						}
					}

					String enbId = enbIdColIndex > -1 ? row[enbIdColIndex] : "";
					String enbName = enbNameColIndex > -1 ? row[enbNameColIndex] : "";
					String duType = duTypeColIndex > -1 ? row[duTypeColIndex] : "";

					if (enbNameColIndex > -1) {
						newEnbNameToRNDCIQEnbInfoData.put(enbName, new String[] { enbId, duType });
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("readDataFromRNDEnbInfoCSV exception!", e);
			Logger.getGmoLogger().printError("Error reading data from RND eNB Info CSV!");
		}
		return newEnbNameToRNDCIQEnbInfoData;
	}

	public static HashMap<String, String[]> readDataFromRNDEUtranParamCSV()
	{
		HashMap<String, String[]> newCellToRNDCIQEUtranParamData = new HashMap<String, String[]>();
		try {
			File rndEUtranParamCSV = getCIQCSVFile("RNDCIQ_EUTRANPARAM");

			if (rndEUtranParamCSV != null && rndEUtranParamCSV.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(rndEUtranParamCSV);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int newCellColIndex = -1;
				int earfcndlColIndex = -1;
				int earfcnulColIndex = -1;
				int dlBwColIndex = -1;
				int ulBwColIndex = -1;
				int noOfTxAntennasColIndex = -1;
				int noOfRxAntennasColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (newCellColIndex < 0 && StringUtil.doesMatch(row[j], "EutranCellFDDId", Pattern.CASE_INSENSITIVE)) {
							newCellColIndex = j;
						}
						else if (earfcndlColIndex < 0 && StringUtil.doesMatch(row[j], "earfcnDl", Pattern.CASE_INSENSITIVE)) {
							earfcndlColIndex = j;
						}
						else if (earfcnulColIndex < 0 && StringUtil.doesMatch(row[j], "earfcnUl", Pattern.CASE_INSENSITIVE)) {
							earfcnulColIndex = j;
						}
						else if (dlBwColIndex < 0 && StringUtil.doesMatch(row[j], "dlChannelBandwidth", Pattern.CASE_INSENSITIVE)) {
							dlBwColIndex = j;
						}
						else if (ulBwColIndex < 0 && StringUtil.doesMatch(row[j], "ulChannelBandwidth", Pattern.CASE_INSENSITIVE)) {
							ulBwColIndex = j;
						}
						else if (noOfTxAntennasColIndex < 0 && StringUtil.doesMatch(row[j], "noOfTxAntennas", Pattern.CASE_INSENSITIVE)) {
							noOfTxAntennasColIndex = j;
						}
						else if (noOfRxAntennasColIndex < 0 && StringUtil.doesMatch(row[j], "noOfRxAntennas", Pattern.CASE_INSENSITIVE)) {
							noOfRxAntennasColIndex = j;
						}
					}

					String newCell = newCellColIndex > -1 ? row[newCellColIndex] : "";
					String earfcndl = earfcndlColIndex > -1 ? row[earfcndlColIndex] : "";
					String earfcnul = earfcnulColIndex > -1 ? row[earfcnulColIndex] : "";
					String dlBw = dlBwColIndex > -1 ? row[dlBwColIndex] : "";
					String ulBw = ulBwColIndex > -1 ? row[ulBwColIndex] : "";
					String noOfTxAntennas = noOfTxAntennasColIndex > -1 ? row[noOfTxAntennasColIndex] : "";
					String noOfRxAntennas = noOfRxAntennasColIndex > -1 ? row[noOfRxAntennasColIndex] : "";

					if (newCellColIndex > -1) {
						newCellToRNDCIQEUtranParamData.put(newCell, new String[] { earfcndl, earfcnul, dlBw, ulBw, noOfTxAntennas, noOfRxAntennas });
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("readDataFromRNDEUtranParamCSV exception!", e);
			Logger.getGmoLogger().printError("Error reading data from RND eUtran Parameters CSV!");
		}
		return newCellToRNDCIQEUtranParamData;
	}

	public static HashMap<String, String[]> readDataFromKGETOptionalFeatureLicenseCSV()
	{
		HashMap<String, String[]> siteToKGETOptionalFeatureLicenseData = new HashMap<String, String[]>();
		try {
			File kgetOptionalFeatureLicenseCSV = new File(FileUtil.getCmCiqDirectory() + File.separator + "KGET_OPTIONALFEATURELICENSE.csv");

			if (kgetOptionalFeatureLicenseCSV.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(kgetOptionalFeatureLicenseCSV);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int nodeMOKeyColIndex = -1;
				int keyIdColIndex = -1;
				int featureStateColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (nodeMOKeyColIndex < 0 && StringUtil.doesMatch(row[j], "NodeMOKey", Pattern.CASE_INSENSITIVE)) {
							nodeMOKeyColIndex = j;
						}
						else if (keyIdColIndex < 0 && StringUtil.doesMatch(row[j], "keyId", Pattern.CASE_INSENSITIVE)) {
							keyIdColIndex = j;
						}
						else if (featureStateColIndex < 0 && StringUtil.doesMatch(row[j], "featureState", Pattern.CASE_INSENSITIVE)) {
							featureStateColIndex = j;
						}
					}

					String site = nodeMOKeyColIndex > -1 ? row[nodeMOKeyColIndex].replaceAll("!.*", "") : "";
					String keyId = keyIdColIndex > -1 ? row[keyIdColIndex] : "";
					String featureState = featureStateColIndex > -1 ? row[featureStateColIndex].replaceAll("[\\s].*", "") : "";

					if (nodeMOKeyColIndex > -1) {
						siteToKGETOptionalFeatureLicenseData.put(site + "!" + keyId, new String[] { featureState });
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("readDataFromKGETOptionalFeatureLicenseCSV exception!", e);
			Logger.getGmoLogger().printError("Error reading data from KGET OptionalFeatureLicense CSV!");
		}
		return siteToKGETOptionalFeatureLicenseData;
	}

	public static HashMap<String, String[]> readDataFromKGETFeatureStateCSV()
	{
		HashMap<String, String[]> siteToKGETFeatureStateData = new HashMap<String, String[]>();
		try {
			File kgetOptionalFeatureLicenseCSV = new File(FileUtil.getCmCiqDirectory() + File.separator + "KGET_FEATURESTATE.csv");

			if (kgetOptionalFeatureLicenseCSV.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(kgetOptionalFeatureLicenseCSV);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int nodeMOKeyColIndex = -1;
				int keyIdColIndex = -1;
				int featureStateColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (nodeMOKeyColIndex < 0 && StringUtil.doesMatch(row[j], "NodeMOKey", Pattern.CASE_INSENSITIVE)) {
							nodeMOKeyColIndex = j;
						}
						else if (keyIdColIndex < 0 && StringUtil.doesMatch(row[j], "keyId", Pattern.CASE_INSENSITIVE)) {
							keyIdColIndex = j;
						}
						else if (featureStateColIndex < 0 && StringUtil.doesMatch(row[j], "featureState", Pattern.CASE_INSENSITIVE)) {
							featureStateColIndex = j;
						}
					}

					String site = nodeMOKeyColIndex > -1 ? row[nodeMOKeyColIndex].replaceAll("!.*", "") : "";
					String keyId = keyIdColIndex > -1 ? row[keyIdColIndex] : "";
					String featureState = featureStateColIndex > -1 ? row[featureStateColIndex].replaceAll("[\\s].*", "") : "";

					if (nodeMOKeyColIndex > -1) {
						siteToKGETFeatureStateData.put(site + "!" + keyId, new String[] { featureState });
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("readDataFromKGETFeatureStateCSV exception!", e);
			Logger.getGmoLogger().printError("Error reading data from KGET FeatureState CSV!");
		}
		return siteToKGETFeatureStateData;
	}

	public static HashMap<String, String[]> readDataFromKGETSwAllocationCSV()
	{
		HashMap<String, String[]> siteToKGETSwAllocationData = new HashMap<String, String[]>();
		try {
			File kgetSwAllocationCSV = new File(FileUtil.getCmCiqDirectory() + File.separator + "KGET_SWALLOCATION.csv");

			if (kgetSwAllocationCSV.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(kgetSwAllocationCSV);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int nodeMOKeyColIndex = -1;
				int keyIdColIndex = -1;
				int featureStateColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (nodeMOKeyColIndex < 0 && StringUtil.doesMatch(row[j], "NodeMOKey", Pattern.CASE_INSENSITIVE)) {
							nodeMOKeyColIndex = j;
						}
						else if (keyIdColIndex < 0 && StringUtil.doesMatch(row[j], "keyId", Pattern.CASE_INSENSITIVE)) {
							keyIdColIndex = j;
						}
						else if (featureStateColIndex < 0 && StringUtil.doesMatch(row[j], "featureState", Pattern.CASE_INSENSITIVE)) {
							featureStateColIndex = j;
						}
					}

					String site = nodeMOKeyColIndex > -1 ? row[nodeMOKeyColIndex].replaceAll("!.*", "") : "";
					String keyId = keyIdColIndex > -1 ? row[keyIdColIndex] : "";
					String featureState = featureStateColIndex > -1 ? row[featureStateColIndex].replaceAll("[\\s].*", "") : "";

					if (nodeMOKeyColIndex > -1) {
						siteToKGETSwAllocationData.put(site + "!" + keyId, new String[] { featureState });
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("readDataFromKGETSwAllocationCSV exception!", e);
			Logger.getGmoLogger().printError("Error reading data from KGET SwAllocation CSV!");
		}
		return siteToKGETSwAllocationData;
	}

	public static HashMap<String, String[]> readDataFromRNDPCICSV()
	{
		HashMap<String, String[]> newCellToRNDCIQPCIData = new HashMap<String, String[]>();
		try {
			File rndPCICSV = new File(FileUtil.getCmCiqDirectory() + File.separator + "RNDCIQ_PCI.csv");

			if (rndPCICSV.exists()) {
				//Build reader instance
				FileReader fr = new FileReader(rndPCICSV);
				CSVReader reader = constructCSVReader(fr, 0);

				//Read all rows at once
				List<String[]> allRows = reader.readAll();

				/*** initialize column index ***/
				int newCellColIndex = -1;
				int sectorIdColIndex = -1;
				int cellIdColIndex = -1;
				int physicalLayerCellIdGroupColIndex = -1;
				int physicalLayerSubCellIdColIndex = -1;
				int rachRootSequenceColIndex = -1;
				for (String[] row : allRows) {
					for (int j = 0; j < row.length; j++) {
						if (newCellColIndex < 0 && StringUtil.doesMatch(row[j], "EutranCellFDDId", Pattern.CASE_INSENSITIVE)) {
							newCellColIndex = j;
						}
						else if (sectorIdColIndex < 0 && StringUtil.doesMatch(row[j], "sectorId", Pattern.CASE_INSENSITIVE)) {
							sectorIdColIndex = j;
						}
						else if (cellIdColIndex < 0 && StringUtil.doesMatch(row[j], "cellId", Pattern.CASE_INSENSITIVE)) {
							cellIdColIndex = j;
						}
						else if (physicalLayerCellIdGroupColIndex < 0 && StringUtil.doesMatch(row[j], "PhysicalLayerCellIdGroup", Pattern.CASE_INSENSITIVE)) {
							physicalLayerCellIdGroupColIndex = j;
						}
						else if (physicalLayerSubCellIdColIndex < 0 && StringUtil.doesMatch(row[j], "physicalLayerSubCellId", Pattern.CASE_INSENSITIVE)) {
							physicalLayerSubCellIdColIndex = j;
						}
						else if (rachRootSequenceColIndex < 0 && StringUtil.doesMatch(row[j], "rachRootSequence", Pattern.CASE_INSENSITIVE)) {
							rachRootSequenceColIndex = j;
						}
					}

					String newCell = newCellColIndex > -1 ? row[newCellColIndex] : "";
					String sectorId = sectorIdColIndex > -1 ? row[sectorIdColIndex] : "";
					String cellId = cellIdColIndex > -1 ? row[cellIdColIndex] : "";
					String physicalLayerCellIdGroup = physicalLayerCellIdGroupColIndex > -1 ? row[physicalLayerCellIdGroupColIndex] : "";
					String physicalLayerSubCellId = physicalLayerSubCellIdColIndex > -1 ? row[physicalLayerSubCellIdColIndex] : "";
					String rachRootSequence = rachRootSequenceColIndex > -1 ? row[rachRootSequenceColIndex] : "";

					if (newCellColIndex > -1) {
						newCellToRNDCIQPCIData.put(newCell, new String[] { sectorId, cellId, physicalLayerCellIdGroup, physicalLayerSubCellId, rachRootSequence });
					}
				}

				//Close
				reader.close();
				fr.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("readDataFromRNDPCICSV exception!", e);
			Logger.getGmoLogger().printError("Error reading data from RND PCI CSV!");
		}
		return newCellToRNDCIQPCIData;
	}

	/**
	 * Read EricssonOnly data from G1 MIM
	 * @param outputFormat
	 * @param softwareLevel
	 * @return
	 */
	public static HashMap<String, HashSet<String>> readEricssonOnlyDataFromG1MIMCSV(String softwareLevel)
	{
		HashMap<String, HashSet<String>> mimData = new HashMap<String, HashSet<String>>();
		try {
			File g1MimFile = new File(FileUtil.getCmCiqDirectory() + File.separator + "Parsed_Mim_G1_" + softwareLevel + ".csv");
			// File g2MimFile = new File(FileUtil.getCmCiqDirectory() + File.separator + "Parsed_Mim_G2_" + softwareLevel + ".csv");

			if (g1MimFile == null || !g1MimFile.exists()) {
				return mimData;
			}

			// Build reader instance
			FileReader fr = new FileReader(g1MimFile);
			CSVReader reader = constructCSVReader(fr, 1);

			// Read all rows at once
			List<String[]> allRows = reader.readAll();

			/**
			 * Read CSV line by line and use the string array as you want
			 * row[0] = CLASS_NAME
			 * row[10] = ATTR_NAME
			 * row[27] = ATTR_VISIBILITY
			 */
			HashSet<String> hs = new HashSet<String>();
			for (String[] row : allRows) {
				if (!row[27].isEmpty()) {
					hs.add(row[0] + "." + row[10]);
				}
			}
			mimData.put("EricssonOnly", hs);

			// Close
			reader.close();
			fr.close();
		}
		catch (Exception e) {
			Logger.logger.error("readEricssonOnlyDataFromG1MIMCSV exception! softwareLevel=" + softwareLevel, e);
			Logger.getGmoLogger().printError("Error reading Ericsson only data from " + softwareLevel + " G1 MIM CSV!");
		}
		return mimData;
	}

	
	/**
	 * Read EricssonOnly data from G1 MIM
	 * @param outputFormat
	 * @param softwareLevel
	 * @return
	 */
	public static HashMap<String, HashSet<String>> readEricssonOnlyDataFromG2MIMCSV(String softwareLevel)
	{
		HashMap<String, HashSet<String>> mimData = new HashMap<String, HashSet<String>>();
		try {
			//File g1MimFile = new File(FileUtil.getCmCiqDirectory() + File.separator + "Parsed_Mim_G1_" + softwareLevel + ".csv");
			 File g2MimFile = new File(FileUtil.getCmCiqDirectory() + File.separator + "Parsed_Mim_G2_" + softwareLevel + "_withEricssonOnly.csv");

			if (g2MimFile == null || !g2MimFile.exists()) {
				return mimData;
			}

			// Build reader instance
			FileReader fr = new FileReader(g2MimFile);
			CSVReader reader = constructCSVReader(fr, 1);

			// Read all rows at once
			List<String[]> allRows = reader.readAll();

			/**
			 * Read CSV line by line and use the string array as you want
			 * row[0] = CLASS_NAME
			 * row[10] = ATTR_NAME
			 * row[27] = ATTR_VISIBILITY
			 */
			HashSet<String> hs = new HashSet<String>();
			for (String[] row : allRows) {
				if (!row[27].isEmpty()) {
					hs.add(row[0] + "." + row[10]);
				}
			}
			mimData.put("EricssonOnly", hs);

			// Close
			reader.close();
			fr.close();
		}
		catch (Exception e) {
			Logger.logger.error("readEricssonOnlyDataFromG2MIMCSV exception! softwareLevel=" + softwareLevel, e);
			Logger.getGmoLogger().printError("Error reading Ericsson only data from " + softwareLevel + " G2 MIM CSV!");
		}
		return mimData;
	}
	/**
	 * Getting Map from ATT_CM_CIQ file
	 * @return
	 */
	public static Map<String, String> readFeatureMapTabFromAttCmCiqCSV()
	{
		Map<String, String> featureMapTabMap = new HashMap<String, String>();
		try {
			File gscCellTabFile = new File(FileUtil.getCmCiqDirectory() + File.separator + "AttCmCiqFeatureStateMap.csv");
			if (gscCellTabFile.exists()) {
				BufferedReader bufferedReader = new BufferedReader(new FileReader(gscCellTabFile));
				String sCurrentLine = bufferedReader.readLine();

				boolean flag = false;
				while (sCurrentLine != null) {
					if (sCurrentLine.startsWith("\"OptionalFeatureLicenseId\"")) {
						flag = true;
					}
					if (flag && !sCurrentLine.startsWith("\"OptionalFeatureLicenseId\"")) {
						String[] bandBWArr = sCurrentLine.split(",");
						if (bandBWArr[0] != null && bandBWArr[0].trim().length() > 0 && bandBWArr[1] != null && bandBWArr[1].trim().length() > 0) {
							featureMapTabMap.put(bandBWArr[1].trim().substring(1, bandBWArr[1].trim().lastIndexOf("\"")), bandBWArr[0].trim().substring(1, bandBWArr[0].trim().lastIndexOf("\"")));
						}
					}
					sCurrentLine = bufferedReader.readLine();
				}
				bufferedReader.close();
			}
		}
		catch (Exception e) {
			logger.error("readFeatureMapTabFromAttCmCiqCSV exception!", e);
			gmoLogger.printError("Read feature map tab from AttCmCiqFeatureStateMap.csv exception! " + e.getMessage());
		}
		return featureMapTabMap;
	}

//	public File fixConvertedRNDCIQ(String inputDir)
//	{
//		File fixedConvertedRNDFile = null;
//		try {
//			/*** fix data ***/
//			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "1st DU type", ".*52.*", "BBU5216");
//			fixDataInColumnInCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "1st DU type", ".*66.*", "BBU6630");
//
//			/*** merge data in CSVs back to RND CIQ ***/
//			LinkedHashMap<File, String> csvFileToSheetName = new LinkedHashMap<File, String>();
//			if (getCIQCSVFile("RNDCIQ_ENBINFO") != null) {
//				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_ENBINFO"), "eNB Info");
//			}
//			if (getCIQCSVFile("RNDCIQ_EUTRANPARAM") != null) {
//				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "eUtran Parameters");
//			}
//			if (getCIQCSVFile("RNDCIQ_PCI") != null) {
//				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_PCI"), "PCI");
//			}
//			if (getCIQCSVFile("RNDCIQ_LOSSESDELAYS") != null) {
//				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_LOSSESDELAYS"), "Losses and Delays");
//			}
//			if (getCIQCSVFile("RNDCIQ_CLUSTER") != null) {
//				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_CLUSTER"), "Cluster");
//			}
//			if (getCIQCSVFile("RNDCIQ_EUTRANNEIGHRELATIONS") != null) {
//				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_EUTRANNEIGHRELATIONS"), "eUtran NeighRelations");
//			}
//			if (getCIQCSVFile("RNDCIQ_EUTRANNEIGHRELATIONSCOSITES") != null) {
//				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_EUTRANNEIGHRELATIONSCOSITES"), "eUtran NeighRelations co-sites");
//			}
//			if (getCIQCSVFile("RNDCIQ_LTEUMTS") != null) {
//				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_LTEUMTS"), "LTE-UMTS (UtranFreqRelation)");
//			}
//			if (getCIQCSVFile("RNDCIQ_LTELTE") != null) {
//				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_LTELTE"), "LTE-LTE (EUtranFreqRelation)");
//			}
//			if (getCIQCSVFile("RNDCIQ_EUTRANINTERFREQRELATIONS") != null) {
//				csvFileToSheetName.put(getCIQCSVFile("RNDCIQ_EUTRANINTERFREQRELATIONS"), "eUtraN interfreq relations");
//			}
//			fixedConvertedRNDFile = CSVUtils.convertCSVToExcel(csvFileToSheetName, inputDir + File.separator + "RNDCIQ_fixed.xls");
//
//			// cleanup
//			fixedConvertedRNDFile = FileUtil.replaceFile(new File(inputDir + File.separator + "RNDCIQ.xls"), fixedConvertedRNDFile);
//		}
//		catch (Exception e) {
//			logger.error("fixConvertedRNDCIQ exception!", e);
//			gmoLogger.printError("Fix converted RND CIQ exception! " + e.getMessage());
//		}
//
//		return fixedConvertedRNDFile;
//	}

	public static Map<String, String> getMOCParamToDefaultValue()
	{
		return mocParamToDefaultValue;
	}
	
	public static Map<String, File> getMOCToCSVFile()
	{
		return mocToKgetCsvFile;
	}

	public static File getKGETCSVFile(String moc)
	{
		File kgetCSVFile = null;
		try {
			if (mocToKgetCsvFile.containsKey(moc)) {
				kgetCSVFile = mocToKgetCsvFile.get(moc);
			}
			else {
				kgetCSVFile = new File(FileUtil.getCmCiqDirectory() + File.separator + "KGET_" + moc.toUpperCase() + ".csv");
			}
		}
		catch (Exception e) {
			logger.error("getKGETCSVFile exception!", e);
			gmoLogger.printError("Get KGET CSV file exception! " + e.getMessage());
		}
		return kgetCSVFile;
	}

	/**
	 * Get value from HashMap from first regex key match
	 */
	public static boolean getValueFromRegexKeyfromhashset(HashSet<String> strToStrHashMap, String regexKey)
	{
		boolean flag = false;
		try {
			for (String entry : strToStrHashMap) {
				if (entry.matches(regexKey)) {
					flag = true;
					break;
				}
			}
		}
		catch (Exception e) {
			logger.error("getValueFromRegexKeyfromhashset exception!", e);
			gmoLogger.printError("Get value from regex key exception! " + e.getMessage());
		}
		return flag;
	}

	/**
	 * Commented temporarily testing in progress 
	 * Convert excel to CSV format with merged row data.
	 * To support merged cell data in GMO_ROGERS-323 Need GMO update to create E41 (E41A or E41B) scripts for Rogers site
	 * @param ciqFile - Excel file
	 * @param sheetName - [regular expression] sheet to extract data from
	 * @param outputCSVFileName - output CSV file name
	 * @return CSV File
	 */
	/*public static File convertCIQCSVReplicateMergeCellData(File ciqFile, String sheetName, String outputCSVFileName)
	{
		File csvFile = null;
		try {
			// TODO Other CUs still need to verify
			String fileExt = ".*\\.xlsx";
			if (GlobalConst.getProject() != null && GlobalConst.getProject().equalsIgnoreCase("T-Mobile")) {	// [05132021 - eusxjas]	Include only for TMO, including Excalibur parsing of Nokia CM data input
				fileExt = ".*\\.xls[xm]";
			}
			if (StringUtil.doesMatch(ciqFile.getPath(), fileExt, Pattern.CASE_INSENSITIVE)) {	// [04022021] Trying this method for case of excessive large sheet in TMO
				PrintStream psTxt = null;
				OPCPackage p = null;
				csvFile = new File(FileUtil.getCmCiqDirectory() + File.separator + outputCSVFileName + ".csv");
				Files.deleteIfExists(csvFile.toPath());
				try {
					psTxt = new PrintStream(csvFile);
					p = OPCPackage.open(ciqFile.getPath(), PackageAccess.READ);
					XLSX2CSV xlsx2CSV = new XLSX2CSV(p, psTxt, -1, sheetName);
					xlsx2CSV.process();
				}
				catch (Exception e) {
					logger.error("Exception!", e);
					return null;
				}
				finally {
					if (psTxt != null) {
						psTxt.flush();
						psTxt.close();
					}
					if (p != null) {
						p.close();
					}
				}
			}
			else {
				csvFile = excel2CSVReplicateMergeCellData(ciqFile, sheetName, outputCSVFileName);
			}
		}
		catch (Exception e) {
			Logger.logger.error("convertCIQCSVReplicateMergeCellData exception! ciqFile=" + ciqFile.getPath() + ", sheetName=" + sheetName + ", outputCSVFileName=" + outputCSVFileName, e);
			Logger.getGmoLogger().printError("Error converting " + ciqFile.getPath() + " \"" + sheetName + "\" to " + outputCSVFileName + "!");
		}
		return csvFile;
	}*/

	/**
	 * Function to consider merged row data
	 * To support merged cell data in GMO_ROGERS-323 Need GMO update to create E41 (E41A or E41B) scripts for Rogers site
	 * @param ciqFile
	 * @param sheetName
	 * @param outputCSVFileName
	 * @return
	 */
	/*public static File excel2CSVReplicateMergeCellData(File ciqFile, String sheetName, String outputCSVFileName)
	{
		try {
			File csvFile = new File(FileUtil.getCmCiqDirectory() + File.separator + outputCSVFileName + ".csv");
			Files.deleteIfExists(csvFile.toPath());
			// in case ciqFile not found
			if (!ciqFile.exists()) {
				return null;
			}

			// Get the workbook object for XLS/XLSX file
			Workbook workbook = WorkbookFactory.create(ciqFile, "", true);
			DataFormatter df = new DataFormatter();

			FileWriter fw = new FileWriter(csvFile.getPath());
			CSVWriter writer = new CSVWriter(fw);

			// Get first sheet from the workbook 
			Sheet sheet = null;
			for (int i = 0; i < workbook.getNumberOfSheets(); i++) {
				if (StringUtil.doesMatch(workbook.getSheetAt(i).getSheetName(), sheetName, Pattern.CASE_INSENSITIVE) && !(workbook.isSheetHidden(i) || workbook.isSheetVeryHidden(i))) {
					sheet = workbook.getSheetAt(i);
					break;
				}
			}

			// in case sheet not found
			if (sheet == null) {
				writer.flushQuietly();
				writer.close();
				fw.close();
				workbook.close();
				Files.deleteIfExists(csvFile.toPath());
				return null;
			}

			// get header row size
			Row headerRow = null;
			for (int i = 0; i < 10; i++) {
				headerRow = sheet.getRow(i);
				if (headerRow != null) {
					break;
				}
			}
			int headerRowSize = 0;
			if (headerRow != null) {
				headerRowSize = headerRow.getLastCellNum();
			}

			Integer numOfRows = sheet.getPhysicalNumberOfRows();
			if (numOfRows > 60000) {			// [09172020] Check for CIQs with more rows than typically found to warn the user if GMO fails to process the inputs.
				Logger.logger.warn("excel2CSV ciqFile=" + ciqFile + ", sheetName='" + sheetName + "', outputCSVFileName='" + outputCSVFileName + "', has a very large number of rows (" + numOfRows.toString() + "). If GMO fails to execute please review this sheet of the CIQ for erroneous or excessive data rows.");
				Logger.getGmoLogger().printWarning("Excel CIQ sheetName='" + sheetName + "', has a very large number of rows (" + numOfRows.toString() + "). If GMO fails to execute, please review the CIQ for erroneous or excessive data rows.");
			}
			if (headerRowSize > 200) {			// [09172020] Check for CIQs or kgets with more columns than typically found. Typically is only sheetName='EUtranCellFDD~', outputCSVFileName='KGET_EUTRANCELLFDD' with 255+ columns
				if (!sheetName.matches("EUtranCell[FT]DD.*"))  {
					Logger.logger.warn("excel2CSV ciqFile=" + ciqFile + ", sheetName='" + sheetName + "', outputCSVFileName='" + outputCSVFileName + "', has a large number of columns (" +  headerRowSize + "). If GMO fails to execute please review this sheet of the CIQ for erroneous or excessive data columns.");
				}
			}

			Integer consecutiveEmptyRowCount = 0;		// If too many empty rows are consecutively encountered then break importing of this sheet
			for (Row row : sheet) {
				if (ServerInfo.isTestServer()) {
					processMergedCellData(sheet.iterator(), sheet);
				}

				// Create record
				ArrayList<String> record = new ArrayList<String>();

				for (int cn = 0; cn < row.getLastCellNum(); cn++) {
					// If the cell is missing from the file, generate a blank one
					// (Works by specifying a MissingCellPolicy)
					Cell cell = row.getCell(cn, Row.CREATE_NULL_AS_BLANK);

					switch (cell.getCellType()) {
						case Cell.CELL_TYPE_BOOLEAN:
							record.add("" + cell.getBooleanCellValue());
							break;

						case Cell.CELL_TYPE_NUMERIC:
							// record.add(Double.toString(cell.getNumericCellValue()).replaceAll("\\.0+$", ""));
							record.add(df.formatCellValue(cell).replaceAll("\\.0+$", ""));
							break;

						case Cell.CELL_TYPE_STRING:
							record.add(cell.getStringCellValue().trim().replaceAll("\"", ""));
							break;

						case Cell.CELL_TYPE_BLANK:
							record.add("");
							break;

						case Cell.CELL_TYPE_FORMULA:
							switch (cell.getCachedFormulaResultType()) {
								case Cell.CELL_TYPE_NUMERIC:
									String cellStringValue = Double.toString(cell.getNumericCellValue());
									cellStringValue = cellStringValue.matches("^.*\\.0$") ? cellStringValue.replaceAll("\\.[\\d]+$", "") : cellStringValue;
									record.add(cellStringValue);
									break;
								case Cell.CELL_TYPE_STRING:
									record.add(cell.getStringCellValue().trim());
									break;
								default:
									record.add("");
									}
							break;

						default:
							record.add("" + cell);
					}
				}

				// padding
				while (record.size() < headerRowSize) {
					record.add("");
				}

				// Write the record to file
				if (record.size() > 0) {
					String[] newArray = new String[record.size()];
					
					Boolean addRecord = true;			// [09172020
					if (addRecord) {					// [09172020
						writer.writeNext(record.toArray(newArray));
					}
				}
			}

			// close the writer
			writer.flushQuietly();
			writer.close();
			fw.close();

			workbook.close();
			return csvFile;
		}
		catch (Exception e) {
			String ciqPath = ciqFile != null ? ciqFile.getPath() : "";
			Logger.logger.error("excel2CSVReplicateMergeCellData exception! ciqFile=" + ciqPath + ", sheetName=" + sheetName + ", outputCSVFileName=" + outputCSVFileName, e);
			Logger.getGmoLogger().printError("Error converting " + ciqPath + " " + sheetName + " to " + outputCSVFileName + "!");
			return null;
		}
	}*/

	/**
	 * Function to process merged cell data
	 * Reference: https://stackoverflow.com/questions/29664977/how-to-read-from-merged-cells-of-excel-in-java-using-apache-poi
	 * @param rowIterator
	 * @param sheet
	 */
	/*private static void processMergedCellData(Iterator<Row> rowIterator, Sheet sheet) {
		try {
			while (rowIterator.hasNext()) {
				Row row = rowIterator.next();

				//For each row, iterate through all the columns
				Iterator<Cell> cellIterator = row.cellIterator();

				outer:
				while (cellIterator.hasNext()) {
					Cell cell = cellIterator.next();

					//will iterate over the Merged cells
					for (int i = 0; i < sheet.getNumMergedRegions(); i++) {
						CellRangeAddress region = sheet.getMergedRegion(i); //Region of merged cells

						int colIndex = region.getFirstColumn(); //number of columns merged
						int rowNum = region.getFirstRow();      //number of rows merged
						//check first cell of the region
						if (rowNum == cell.getRowIndex() && colIndex == cell.getColumnIndex()) {
							System.out.println(sheet.getRow(rowNum).getCell(colIndex).getStringCellValue());
							continue outer;
						}
					}
					//the data in merge cells is always present on the first cell. All other cells(in merged region) are considered blank
					if (cell.getCellType() == Cell.CELL_TYPE_BLANK || cell == null) {
						continue;
					}
					System.out.println(cell.getStringCellValue());
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("processMergedCellData exception! sheetName=" + sheet, e);
			Logger.getGmoLogger().printError("Error processing " + sheet + " with merged row data !");
		}
	}*/

}
