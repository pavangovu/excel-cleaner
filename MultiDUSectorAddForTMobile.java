package com.ericsson.utran.tools.tmo_ericsson;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TimeZone;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

import javax.xml.XMLConstants;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.apache.commons.lang.ArrayUtils;
import org.eclipse.persistence.oxm.record.OutputStreamRecord;
import org.w3c.dom.DOMImplementation;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import com.ericsson.utran.tools.GlobalConst;
import com.ericsson.utran.tools.GmoExecuter;
import com.ericsson.utran.tools.Mongo;
import com.ericsson.utran.tools.RemoteTemplate;
import com.ericsson.utran.tools.Tools;
import com.ericsson.utran.tools.c2gconnector.C2GDBProcessor;
import com.ericsson.utran.tools.common.ErrorCategory;
import com.ericsson.utran.tools.common.ErrorSubcategory;
import com.ericsson.utran.tools.converter.COException;
import com.ericsson.utran.tools.esi.EsiCsvHeader;
import com.ericsson.utran.tools.mom.AntennaUnitGroupObj;
import com.ericsson.utran.tools.mom.GNodeBSectorCarrierObj;
import com.ericsson.utran.tools.mom.GsmCell;
import com.ericsson.utran.tools.mom.NRCellObj;
import com.ericsson.utran.tools.mom.RfBranchObj;
import com.ericsson.utran.tools.mom.SectorEquipmentFunctionObj;
import com.ericsson.utran.tools.mom.SiteCellObj;
import com.ericsson.utran.tools.mom.WCDMACell;
import com.ericsson.utran.tools.scripts.MOScripts;
import com.ericsson.utran.tools.scripts.MOScripts5GNR;
import com.ericsson.utran.tools.scripts.NetconfScripts;
import com.ericsson.utran.tools.scripts.ParamPreservation;
import com.ericsson.utran.tools.scripts.ScriptValidation;
import com.ericsson.utran.tools.scripts.XMLScripts;
import com.ericsson.utran.tools.shared.CMCIQUtil;
import com.ericsson.utran.tools.shared.CSVUtils;
import com.ericsson.utran.tools.shared.CiqConstants;
import com.ericsson.utran.tools.shared.CleanUtil;
import com.ericsson.utran.tools.shared.CommonUtil;
import com.ericsson.utran.tools.shared.FileUtil;
import com.ericsson.utran.tools.shared.GmoNotificationUtil;
import com.ericsson.utran.tools.shared.KgetUtil;
import com.ericsson.utran.tools.shared.LkffetchUtil;
import com.ericsson.utran.tools.shared.Logger;
import com.ericsson.utran.tools.shared.S2GUtils;
import com.ericsson.utran.tools.shared.ServerInfo;
import com.ericsson.utran.tools.shared.StringUtil;
import com.ericsson.utran.tools.shared.SystemConstants;
import com.ericsson.utran.tools.srs.TMO_SRS_Generator;
import com.ericsson.utran.tools.tmo.cpri_remapping.TMOCPRIRemappingProject;
import com.ericsson.utran.tools.tmo.fingerprintalignment.FingerprintAlignment;
import com.opencsv.CSVReader;

public class MultiDUSectorAddForTMobile implements TMOConfigChangeRecorderInterface
{
	private HashMap<String, File> ciqs;
	private MOScripts moScripts;
	private MOScripts5GNR moScripts5GNR;
	private NetconfScripts netconfScripts;
	private Set<String> sites;
	private String inputDir;
	private String outputDir;
	private String siteList;
	private TMO_Config_Change_Recorder tmoCCR;
	//private TMO_TDD_MixedModeBaseBandScripts tmoTDDMMBB;
	private XMLScripts xmlScripts;
	private static boolean has5GSites = false;
	private static boolean has2GSites = false;
	private static boolean has3GSites = false;
	private static boolean has2GAnd3GSites = false;
	private TmoFileRenamingForESI tmoFileRenamingForESI;
	private TMODataCollector tmoDC;
	private GmoExecuter gmoExecuter;
	private boolean isMDUScope;
	private boolean ignoreValidationDialog;

	private boolean isTestServer;
	private GenericScriptBlockGenerator genericScriptBlockGenerator;
	private boolean hasExcalibur4G5G = false;
	private boolean hasDataPortMismatchSites = false;
	private boolean generateExcalibur = false;
	private boolean isSiteInfoExists = false;
	private static boolean isExcaliburToSB = false;
	private boolean hasExcaliburSmallCells = false;
	
	
	//Technology Constant
	private static final String NSB_4G_OR_5G_TECHNOLOGY = "NSB 4G or 5G";
	private static final String NSB_2G_OR_3G_TECHNOLOGY = "NSB 2G or 3G";

	
	public MultiDUSectorAddForTMobile(String inputDir, String siteList, String outputDir)
	{
		ciqs = new HashMap<String, File>();
		this.inputDir = inputDir;
		this.outputDir = outputDir;
		this.siteList = siteList;
		moScripts = new MOScripts();
		moScripts5GNR = new MOScripts5GNR();
		netconfScripts = new NetconfScripts();
		xmlScripts = new XMLScripts();
		isTestServer = ServerInfo.isTestServer();
		setTmoFileRenamingForESI(new TmoFileRenamingForESI());
		initializeInputs(NSB_4G_OR_5G_TECHNOLOGY);
	}
	
	public MultiDUSectorAddForTMobile(String inputDir, String siteList, String outputDir, String technology) {
		ciqs = new HashMap<String, File>();
		this.inputDir = inputDir;
		this.outputDir = outputDir;
		this.siteList = siteList;
		moScripts = new MOScripts();
		moScripts5GNR = new MOScripts5GNR();
		netconfScripts = new NetconfScripts();
		xmlScripts = new XMLScripts();
		isTestServer = ServerInfo.isTestServer();
		setTmoFileRenamingForESI(new TmoFileRenamingForESI());
		initializeInputs(technology);
	}

	// [eusxjas - 06272019]	for file renaming
	public MultiDUSectorAddForTMobile(String inputDir)
	{
		this.inputDir = inputDir;
		isTestServer = ServerInfo.isTestServer();
		setTmoFileRenamingForESI(new TmoFileRenamingForESI());
		genericScriptBlockGenerator = new GenericScriptBlockGenerator();
	}

	// [eusxjas - 04122021]	for script block generation TC_400
	public MultiDUSectorAddForTMobile()
	{
		isTestServer = ServerInfo.isTestServer();
	}

	/**
	 * Initialize inputs
	 */
	public void initializeInputs(String technology)
	{
		try {
			GmoExecuter.initCommonElements(outputDir);

			// sites
			sites = CommonUtil.getSiteListMatrixSet(siteList);
			
			//[04052021 - ezrxxsu] - Physical and Logical Dataport Mismatch - TC_403
			initRilinkData(inputDir, ciqs);
			
			// download the TMO LTE 5G Daily Report file
			if(!hasDataPortMismatchSites) {
				initTmoDailyReport4G5G();	// [06242020] TC_311
			}
			
			if(technology.equals("Excalibur 4G or 5G")) {
				hasExcalibur4G5G = true;
			}
				
			if(technology.equals("Generate Excalibur Scripts")) {
				generateExcalibur = true;
				hasExcalibur4G5G = true;
			}
			
			if (hasExcalibur4G5G || NSB_2G_OR_3G_TECHNOLOGY.equals(technology)) {
				initExcaliburCMCIQ(ciqs);
			}
			
			if(!hasExcalibur4G5G && !NSB_2G_OR_3G_TECHNOLOGY.equals(technology) && !hasDataPortMismatchSites) {
				// retrieve KGET data
				initKGETData(inputDir);
			}
			
			boolean isInputDirEmpty=false;
			if(NSB_2G_OR_3G_TECHNOLOGY.equals(technology) || hasExcalibur4G5G) {
				
				File inputDirFile = new File(inputDir);
				if(inputDirFile.isDirectory()) {
					String[] fileList = inputDirFile.list();
					for(String fileName : fileList) {
						if(fileName.endsWith(".xlsx") || fileName.endsWith(".csv")) {
							Logger.getGmoLogger().printHeaderTextWithTimeStamp("The file in the input folder is " + fileName);
							isInputDirEmpty = true;
							break;
						}
					}
				}
			}
			
			if(!isInputDirEmpty && (NSB_2G_OR_3G_TECHNOLOGY.equals(technology) || hasExcalibur4G5G || technology.equals("Generate Excalibur Scripts"))) {
//				1 check input
//				2 check c2g
				initC2GDb();
				Logger.logger.warn("Fetching the CIQ's from C2G");
				Logger.getGmoLogger().printWarning("Fetching the CIQ's from C2G");
              //3 check mongo
              //initMongoData();
			}
			else if((NSB_2G_OR_3G_TECHNOLOGY.equals(technology) || hasExcalibur4G5G)) {
				Logger.logger.warn("Fetching the Physical CIQ's");
				Logger.getGmoLogger().printWarning("Fetching the Physical CIQ's");
			}
			
			if((NSB_2G_OR_3G_TECHNOLOGY.equals(technology) || hasExcalibur4G5G)) 
			{
				ciqs.put("Excalibur_SiteInfo", new File(inputDir + File.separator + "TMobile_Excalibur_SITE_INFO.xlsx"));
				File siteInfoCSV = CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_SiteInfo"), "siteInfo", "siteInfo");
				if(siteInfoCSV!=null) {
					List<String> lines = Files.readAllLines(siteInfoCSV.toPath());
					String site = "";
					for (String p : sites) {
						site = p;
						break;
					}
					if(lines.size() > 1) {
						isSiteInfoExists = true;
						String technologies = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("siteInfo"), "Site Name", site, "Technologies");
						String siteScope = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("siteInfo"), "Site Name", site, "scope");
						if(siteScope != null && !siteScope.isEmpty()) {
							if (siteScope.equals("ToSB")) {
								isExcaliburToSB = true;
							}
						}
					}
					else {
						Logger.logger.error("Site Info is empty, Please contact CIQ team");
						Logger.getGmoLogger().printError("Site Info is empty, Please contact CIQ team");
					}
				}
				else {
					Logger.logger.error("Site Info file is not found, Please contact CIQ team");
					Logger.getGmoLogger().printError("Site Info is not found, Please contact CIQ team");
				}
				
			}
			
			if(NSB_2G_OR_3G_TECHNOLOGY.equals(technology) || generateExcalibur) {
				c2gExcaliburMongo();
			}
			
			if(technology.equals("Generate Excalibur Scripts")) {
				Set<String> tempsites = new HashSet<>();
				for (String site : sites) {
					tempsites.addAll(getSiteListFromRNDCIQFile(site));

				}
				sites = tempsites;
				if(has2GAnd3GSites) {
					sites.addAll(CommonUtil.getSiteListMatrixSet(siteList));
				}	
			}
			else if (hasExcalibur4G5G && !NSB_2G_OR_3G_TECHNOLOGY.equals(technology)) {
				Set<String> tempsites = new HashSet<>();
				for (String site : sites) {
					tempsites.addAll(getSiteListFromRNDCIQFile(site));

				}
				sites = tempsites;
			}
			
			// retrieve market data
			TMO_CommonUtil.initMarketData(ciqs);

			// retrieve CMCIQ data
			TMO_CommonUtil.initCMCIQData(inputDir, ciqs);
			
			if(!NSB_2G_OR_3G_TECHNOLOGY.equals(technology) && !hasDataPortMismatchSites) {
				// retrieve TND data
				initTNDData(inputDir, ciqs, siteList);
			}
			// retrieve MongoData
			//if (NSB_2G_OR_3G_TECHNOLOGY.equals(technology) && SystemConstants.EXCALIBUR_USERS.matches(".*" + SystemConstants.userSignum + ".*")) {
				//initMongoData();
			//}

			// retrieve TMO SCU data
			initSCUData(inputDir, ciqs);
			
			TMO_CommonUtil.initENMAutoprovisioningZipFiles(inputDir);
			if (isTestServer)	{			// [04132022] GMO_TMO-274
				TMO_CommonUtil.initMigFilZipFiles(inputDir);
			}

			boolean rndExists=false;
			if(!NSB_2G_OR_3G_TECHNOLOGY.equals(technology) && !hasDataPortMismatchSites) {
				// retrieve RND data
				 rndExists = initRNDData(inputDir, ciqs, siteList);
			}
						
			/*** TMO_Config_Change_Recorder ***/
			Logger.logger.debug("Collecting data for [" + String.join(", ", sites) + "]");
			Logger.getGmoLogger().printTextWithTimeStamp("Collecting data for [" + String.join(", ", sites) + "]");
			tmoCCR = new TMO_Config_Change_Recorder();
			tmoDC = new TMODataCollector(tmoCCR);
			genericScriptBlockGenerator = new GenericScriptBlockGenerator();
			tmoCCR.setInputDir(inputDir);
			tmoCCR.setOutputDir(outputDir);
			tmoCCR.setRndExists(rndExists);
			tmoCCR.has5GSites = has5GSites;
			tmoCCR.has2GSites = has2GSites;
			tmoCCR.has3GSites = has3GSites;
			tmoCCR.has2GAnd3GSites = has2GAnd3GSites;
			tmoCCR.hasExcalibur4G5G = hasExcalibur4G5G;
			tmoCCR.hasDataPortMismatchSites = hasDataPortMismatchSites;
			if(hasExcalibur4G5G) {
				for(String site:sites) {
					String config = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GNBINFO"), "gNB Name", site, "ConfigurationType");
					if(config.startsWith("SC-593H")) {
						hasExcaliburSmallCells = true;
						tmoCCR.hasExcaliburSmallCells = true;
					}
				}
			}
			
			// [eshinai: 053019] If it is S2G, you only got one 5G site name.
			if(tmoCCR.has5GSites){
				// you have 5G sites. sort them all alphabetically
				sites = sortSiteNames(sites);
			}
			
			if(hasDataPortMismatchSites) {
				tmoCCR.collectDataForDataPortMismatch(sites, ciqs);
			}
			else {
				tmoCCR.generateExistingTargetData(sites, ciqs);
			}
			
			if(hasExcalibur4G5G) {
				Pattern radio4460 = Pattern.compile(".*4460");
				Pattern radio4460Regex=Pattern.compile("-*4460*");
				Pattern radio4480 = Pattern.compile(".*4480");
				for(String site:sites) {
					SiteCellObj cellObj = tmoCCR.getDUToDUInfo().get(site);
					Set<String> p = cellObj.tmoDUInfo.radioTypeSet;
					for(Map.Entry<String, SiteCellObj> cellInfoEntry : cellObj.newCellToCellInfo.entrySet()) {
						SiteCellObj cellInfo = cellInfoEntry.getValue();
						if (cellObj!=null && cellInfo!=null) {
							if (cellInfo.radioType != null
									&& (radio4460Regex.matcher(cellInfo.radioType).find() || radio4460.matcher(cellInfo.radioType).find() || radio4480.matcher(cellInfo.radioType).find() ||cellInfo.radioType.matches("A.*4460") || cellInfo.radioType.matches("R.*4460")|| cellInfo.radioType.matches("A.*4480") || cellInfo.radioType.matches("R.*4480") )) {					
								Logger.logger.warn("Site cell object radio type value contains 4460 or 4480 for site :" + cellInfo.cellName);
								Logger.getGmoLogger().printWarning("Site cell object radio type value contains 4460 or 4480 for site :" + cellInfo.cellName);
							}
						}
					}
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("initializeInputs exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error initializing inputs! " + e.getMessage());
		}
	}
	
	private void initExcaliburCMCIQ(HashMap<String, File> ciqs2) {
		try {
			RemoteTemplate.getXLSFileFromServer("templates/marketdata/tmobile/" + TMOConstants.tmoCMCIQ.get("Excalibur_CM_CIQ"), FileUtil.getCmCiqDirectory() + File.separator + TMOConstants.tmoCMCIQ.get("Excalibur_CM_CIQ"), false);
			ciqs.put("Excalibur_CMCIQ", new File(FileUtil.getCmCiqDirectory() + File.separator + TMOConstants.tmoCMCIQ.get("Excalibur_CM_CIQ")));
			
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "LTE_NR", "Excalibur_CM_CIQ_LTE_NR");
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "Sector_Carrier", "Excalibur_CM_CIQ_Sector_Carrier");
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "RiPort_Radio_Table_Radio4460", "Excalibur_CM_CIQ_RiPort_radio4460");
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "RiPort_Radio_Table_Radio4402", "Excalibur_CM_CIQ_RiPort_radio4402");
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "RiPort_Radio_Table_Radio4455", "Excalibur_CM_CIQ_RiPort_radio4455");
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "RiPort_Radio_Table_Radio4435", "Excalibur_CM_CIQ_RiPort_radio4435");
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "RBB", "Excalibur_CM_CIQ_RBB");
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "RiPort_Radio_Table", "Excalibur_CM_CIQ_RiPort");
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "SW_Lvl_Map_BB_type", "Excalibur_CM_CIQ_SW_LVL");
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "ExcaliburRadios", "Excalibur_ExcaliburRadios");
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "Excalibur_SpecialSites", "Excalibur_Special_Sites");
			CSVUtils.convertCIQToCSV(ciqs.get("Excalibur_CMCIQ"), "ExcaliburBands", "Excalibur_Bands");
		}
		catch(Exception e) {
			Logger.logger.error("Error Initializing the Excalibur CMCIQ", e);
		}
	}

	public Map<String, ArrayList<String>> getSiteNameEutranCellFDDId(List<String> sites) throws IOException {
		Map<String, ArrayList<String>> siteNameList = new HashMap<>();
		Map<String, ArrayList<String>> result = new HashMap<>();
		Map<String, ArrayList<String>> eutranClellList = new HashMap<>();
		File rndFile = CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO");
		File ultraParam = CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM");

		siteNameList = getColumnValuesForKey(rndFile, "eNodeB Name", "eNBId");
		eutranClellList = getColumnValuesForKey(ultraParam, "eNBId", "EutranCellFDDId");

		for (Map.Entry<String, ArrayList<String>> entry : siteNameList.entrySet()) {
			if (sites.contains(entry.getKey())) {
				for (String enbId : entry.getValue()) {
					result.put(entry.getKey(), eutranClellList.get(enbId));
				}
			}
		}

		return result;
	}

	private Set<String> getSiteListFromRNDCIQFile(String site) throws IOException {
		List<String> files = FileUtil.getFilePathsFromFolder(inputDir, ".*[Cc][Ii][Qq].*\\.(xls|xlsx|xlsm)$", false);
		File rndFile;
		File nbiInfoCsv;
		Set<String> cellId = new HashSet<>();
		for (String file : files) {
			Integer lastDirIndex = file.lastIndexOf("\\") < 0 ? -1 : file.lastIndexOf("\\");	// Get full path/file name or just file name in next line
			String fileOnly = file.substring(lastDirIndex + 1);		// [10282019] In case directory path has "TND" in subdirectory name.
			String skipProcessingFileOnlyRegex = ".*[Tt][Nn][Dd].*";
			if (!fileOnly.matches(skipProcessingFileOnlyRegex)) {
				rndFile = new File(file);
				if (CSVUtils.checkIfsheetExistsInExcel(rndFile, TMOConstants.eNBInfoSheetName)) {

					nbiInfoCsv = CSVUtils.convertCIQToCSV(rndFile, TMOConstants.eNBInfoSheetName, "RND_NBINFO");
					cellId.addAll(getColumnValues(nbiInfoCsv, site, "eNodeB Name"));
					if((cellId == null || cellId.isEmpty())) {
						cellId.addAll(getExcaliburSmallCellColumnValues(nbiInfoCsv, site, "eNodeB Name"));
					}
				}
			}
		}
		return cellId;
	}

	
	/**
	 * Initialize initC2GDb data
	 */
	private boolean initC2GDb() {
		try {
			Logger.getGmoLogger().printTextWithTimeStamp("initC2GDatabase:::");
			Logger.getGmoLogger().printTextWithTimeStamp("sites:::" + sites.toString());
			HashSet<String> collections = new HashSet<>(Arrays.asList("cluster", "rbsSite", "dynRn", "cell",
					"lossesAndDelays", "dipDetails", "lacSacRac", "transportciqless2gand3g","gsmextcell","UMTSLTERelations","GSMLTERelation", "Cluster_LTE",
		            "EnbInfo",
		            "GNBInfo",
		            "GUtranCellInfo",
		            "LossesAndDelay_LTE",
		            "PCI",
		            "eUtranParameters",
		            "transportciqless4g",
		            "transportciqless5g",
		            "EUtranNeighRelationsCoSites",
		            "LTELTEFreqRelation",
		            "AsymmetricReconfigs",
		            "CascadedRETDevices",
		            "LTECarrierAggregation",
		            "LTEUMTSUtranFreqRelations",
		            "UMTSLTERelations",
		            "LTEGSMFreqGroupRel",
		            "LTEGSMGeranFreqGroup",
		            "LTEGSMCells",
		            "GSMLTERelation",
		            "L2GCells",
		            "LTENRFreqRelation",
		            "NRLTEFreqRelation",
		            "NRNRFreqRelations",
		            "NBIoT",
		            "L2L",
		            "L2LFREQR",
		            "L2GFREQ",
		            "LTE2GSM",
		            "L2U",
		            "L2UCells",
		            "U2LFreq",
		            "L2UFreq",
		            "L2URel",
		            "NRCarrierAggregation"));
			new C2GDBProcessor("T-Mobile",inputDir,collections,sites);
		}
		catch (Exception e) {
			e.printStackTrace();
			Logger.logger.error("Error:Init c2g database Exception!", e);
			return false;
		}
		return true;
	}
	
	
	public Set<String> getColumnValues(File nbiInfoCsv, String site, String columnName) throws IOException {
		Set<String> cellId = new HashSet<>();
		FileReader fr = null;
		try {
			fr = new FileReader(nbiInfoCsv);

			CSVReader reader = CSVUtils.constructCSVReader(fr, 0);
			String[] record = null;
			int i = 0;
			int headerIndex = 0;
			while ((record = reader.readNext()) != null) {
				if (i == 0) {
					for (int j = 0; j < record.length; j++) {
						if (columnName.equals(record[j])) {
							headerIndex = j;
						}
					}
				} else {
					if (record[headerIndex] != null && record[headerIndex].contains(site)) {
						cellId.add(record[headerIndex]);
					}
				}
				i++;
			}
			reader.close();

		} catch (Exception e) {
		}

		if (fr != null)
			fr.close();

		return cellId;
	}
	
	public Set<String> getExcaliburSmallCellColumnValues(File nbiInfoCsv, String site, String columnName) throws IOException {
		Set<String> cellId = new HashSet<>();
		FileReader fr = null;
		try {
			fr = new FileReader(nbiInfoCsv);

			CSVReader reader = CSVUtils.constructCSVReader(fr, 0);
			String[] record = null;
			int i = 0;
			int headerIndex = 0;
			while ((record = reader.readNext()) != null) {
				if (i == 0) {
					for (int j = 0; j < record.length; j++) {
						if (columnName.equals(record[j])) {
							headerIndex = j;
						}
					}
				} else {
					if (record[headerIndex] != null && !record[headerIndex].contains(site)) {
						cellId.add(record[headerIndex]);
					}
				}
				i++;
			}
			reader.close();

		} catch (Exception e) {
		}

		if (fr != null)
			fr.close();

		return cellId;
	}


	private Map<String, ArrayList<String>> getColumnValuesForKey(File nbiInfoCsv, String firstCol, String secColumn) throws IOException {
		Map<String, ArrayList<String>> map = new HashMap<>();
		FileReader fr = null;
		try {
			fr = new FileReader(nbiInfoCsv);

			CSVReader reader = CSVUtils.constructCSVReader(fr, 0);
			String[] record = null;
			int i = 0;
			int firstHeader = 0;
			int secHeader = 0;
			while ((record = reader.readNext()) != null) {
				if (i == 0) {
					for (int j = 0; j < record.length; j++) {
						if (firstCol.equals(record[j])) {
							firstHeader = j;
						}
						if (secColumn.equals(record[j])) {
							secHeader = j;
						}
					}
				} else {
					if (record[firstHeader] != null) {
						ArrayList<String> list = map.get(record[firstHeader]);
						if (list != null) {
							list.add(record[secHeader]);
						} else {
							list = new ArrayList<>();
							list.add(record[secHeader]);
							map.put(record[firstHeader], list);
						}
					}
				}
				i++;
			}
			reader.close();

		} catch (Exception e) {
		}

		if (fr != null)
			fr.close();

		return map;
	}

	/**
	 * Initialize RND data
	 * @return true if successful, otherwise false
	 */
	public boolean initRNDData(String inputDir, HashMap<String, File> ciqs, String siteList)
	{
		boolean atLeastOneRNDCIQFileExists = true;
		try {
			
			//Filter the data
	        String siteSubStrListPiped = "!";
	        // Build SiteSubStr list for filter
	        if(sites != null && !sites.isEmpty()) {
		        for(String site: sites) {
		        	String siteSubStr = "";
	        		siteSubStr = site.replaceAll("^[A-Za-z]", "").replaceAll("[\\d]$", "");
	        		if (!StringUtil.doesMatch(siteSubStrListPiped, ".*!" + siteSubStr + "!.*", Pattern.CASE_INSENSITIVE)){
	        			siteSubStrListPiped = siteSubStrListPiped + siteSubStr + "!";
	        		}
		        }
	        }
	        siteSubStrListPiped = siteSubStrListPiped.replaceAll("^!", "").replaceAll("!$", "").replaceAll("!", "\\|");
	        
			// locate RND file
			String rndFile = null;
			List<String> files = FileUtil.getFilePathsFromFolder(inputDir, ".*[Cc][Ii][Qq].*\\.(xls|xlsx|xlsm)$", false);
			for (String file : files) {
				Integer lastDirIndex = file.lastIndexOf("\\") < 0 ? -1 : file.lastIndexOf("\\");	// Get full path/file name or just file name in next line
				String fileOnly = file.substring(lastDirIndex + 1);		// [10282019] In case directory path has "TND" in subdirectory name.
				String skipProcessingFileOnlyRegex = ".*[Tt][Nn][Dd].*";
				if (!fileOnly.matches(skipProcessingFileOnlyRegex)) {
					if(! new File(file).getName().startsWith("~$")) {
						rndFile = file;
						
						//[egovpav]
						//remove excess rows and columns before proceeding
						rndFile = CSVUtils.cleanExcel(rndFile);
						
						ciqs.put("RND", new File(rndFile));

						ArrayList<String> rndSheetsToProcess = new ArrayList<String>();
						ArrayList<String> rndSheetToProcessMMBB = new ArrayList<String>();
						ArrayList<String> rndSheetsToProcess5G = new ArrayList<String>();
						
						if(CSVUtils.checkIfsheetExistsInExcel(new File(rndFile),TMOConstants.eNBInfoSheetName)) {
							rndSheetsToProcess = TMOConstants.rndSheetsToProcess;
							CSVUtils.convertRNDToCSV(ciqs.get("RND"), rndSheetsToProcess);
							if(CSVUtils.checkIfsheetExistsInExcel(new File(rndFile),TMOConstants.gNBInfoSheetName)) {
								rndSheetToProcessMMBB = TMOConstants.rndSheetToProcessMMBB;
								CSVUtils.convertRNDToCSV(ciqs.get("RND"), rndSheetToProcessMMBB);
							}
						}else {
							rndSheetsToProcess5G = TMOConstants.rndSheetsToProcess5G;
							CSVUtils.convertRNDToCSV(ciqs.get("RND"), rndSheetsToProcess5G);
						}

						ArrayList<String> sheetsToProcess = new ArrayList<String>();
						sheetsToProcess = TMOConstants.tmoSheetsToProcessForNSB;

						for (String sheet : sheetsToProcess) {
							if(CSVUtils.existsAndNotEmpty(CSVUtils.getCIQCSVFile("RNDCIQ" + "_" + CiqConstants.ciqSheetToCSVFileTag.get(sheet)), false)) {
								if(TMOConstants.tmoSheetNameToColumnFilterMap.get(sheet) != null && !TMOConstants.tmoSheetNameToColumnFilterMap.get(sheet).isEmpty()) {
									CSVUtils.filterDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ" + "_" + CiqConstants.ciqSheetToCSVFileTag.get(sheet)), TMOConstants.tmoSheetNameToColumnFilterMap.get(sheet), ".*(" + siteSubStrListPiped + ").*");
									FileUtil.deleteFile(FileUtil.getCmCiqDirectory() + File.separator + "RNDCIQ" + "_" + CiqConstants.ciqSheetToCSVFileTag.get(sheet) + ".csv");
									FileUtil.renameFile(FileUtil.getCmCiqDirectory() + File.separator + "RNDCIQ" + "_" + CiqConstants.ciqSheetToCSVFileTag.get(sheet) + "_Filtered.csv" , FileUtil.getCmCiqDirectory() + File.separator + "RNDCIQ" + "_" + CiqConstants.ciqSheetToCSVFileTag.get(sheet) + ".csv");
								}
							}
						}

						// if 4G RND data not available, Check for 5G RND Data
						if ((!CSVUtils.existsAndNotEmpty(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), false))){
							atLeastOneRNDCIQFileExists = false;
						}
						if(hasExcalibur4G5G) {
							CSVUtils.convertCIQToCSV(ciqs.get("RND"), "NR-LTE- FreqRelation", "RNDCIQ_NR-LTE");
						}
						if ((!CSVUtils.existsAndNotEmpty(CSVUtils.getCIQCSVFile("RNDCIQ_GNBINFO"), false))){
							if (!atLeastOneRNDCIQFileExists) {
								Logger.getGmoLogger().printWarning("Unable to extract RND data. Process stopped.");
								return false;
							}
						}
						else {
							atLeastOneRNDCIQFileExists = true;
						}
					}
				}
			}
			if (rndFile == null || rndFile.isEmpty()) {
				Logger.getGmoLogger().printWarning("Unable to locate RND file in " + inputDir + ".");
				return false;
			}
			
			Logger.getGmoLogger().printTextWithTimeStamp("Extracted data from local RND file.");
		}
		catch (Exception e) {
			Logger.logger.error("initRNDData exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error initializing RND data! " + e.getMessage());
			return false;
		}
		return atLeastOneRNDCIQFileExists;
	}
		
	/**
	 * Function to initialize TMO Daily Report csv file
	 */
	// [06242020] Copied exactly from MultiDUSectorAddScriptsTMobile
	public void initTmoDailyReport4G5G()
	{
		try
		{
			RemoteTemplate.getXLSFileFromServer("templates/marketdata/tmobile/" + TMOConstants.TMOLTE5GDAILYREPORT + ".csv", FileUtil.getCmCiqDirectory() + File.separator + TMOConstants.TMOLTE5GDAILYREPORT + ".csv", false);
			Logger.logger.info("Copying TMO Daily Report csv file to CMCIQ folder....");
		}
		catch(Exception ex)
		{
			Logger.getGmoLogger().printError("Error while fetching TMO Daily Report csv file.");
		}
	}
	
	/**7yguze5z
	 * Initialize TND data
	 * @return true if successful, otherwise false
	 */
	public boolean initTNDData(String inputDir, HashMap<String, File> ciqs, String siteList)
	{
		try {
			has5GSites = false;		// [02112021] Reset just to be sure value from prior GMO run is carried to next GMO run
			
			// locate TND file
			String atndFile = FileUtil.getFilePathFromFolder(inputDir, ".*[Tt][Nn][Dd].*\\.(xls|xlsx|xlsm)$", false);
			if (atndFile == null || atndFile.isEmpty()) {
				boolean noTndFileFound = true;
				ArrayList<String> atndFiles = FileUtil.getFilePathsFromFolder(inputDir, ".*\\.(xls|xlsx|xlsm)$", false);
				for (String atndFilePath:atndFiles) {
					File atnd4G5GCSV = CSVUtils.convertCIQToCSV(new File(atndFilePath), "Sheet1", "ATND_ENODEB_GNODEB");
					if (CSVUtils.existsAndNotEmpty(atnd4G5GCSV, false)) {
						List<String> headerKeys = new ArrayList<String>();
						headerKeys.add("Nodename");
						headerKeys.add("Enbid");
						headerKeys.add("Gnbid");
						atnd4G5GCSV = CSVUtils.filterNonHeaderRows(atnd4G5GCSV, headerKeys);
						CSVUtils.setCIQCSVFile("ATND_ENODEB_GNODEB", atnd4G5GCSV);
						atndFile = atndFilePath;
						noTndFileFound = false;
					}
				}

				if (noTndFileFound) {
					Logger.getGmoLogger().printWarning("Unable to locate required TND file in " + inputDir + ".");
					return false;
				}
			}
			
			ciqs.put("ATND", new File(atndFile));
			try {Logger.logger.debug("In 412 ciqs(ATND) is: " + ciqs.get("ATND").getAbsolutePath());}catch(Exception ex) {Logger.logger.debug("In 412 ciqs(ATND) is null"); }

			// convert 4G ATND to CSV
			File atndCSV = CSVUtils.convertCIQToCSV(ciqs.get("ATND"), "eNodeB Ericsson", "ATND_ENODEB");
			if (CSVUtils.existsAndNotEmpty(atndCSV, false)) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("eNodeB name");
				headerKeys.add("eNodeB ID");
				atndCSV = CSVUtils.filterNonHeaderRows(atndCSV, headerKeys);
				CSVUtils.setCIQCSVFile("ATND_ENODEB", atndCSV);
			}
			else {
				if (!CSVUtils.checkIfsheetExistsInExcel(new File(atndFile),"eNodeB Ericsson")) {
					atndFile = FileUtil.getFilePathFromFolder(inputDir, TMOConstants.tmo4GATNDFileNameRegex, false);
					if (!atndFile.isEmpty()) {
						ciqs.put("ATND", new File(atndFile));
						try {Logger.logger.debug("In 430 ciqs(ATND) is: " + ciqs.get("ATND").getAbsolutePath());}catch(Exception ex) {Logger.logger.debug("In 430 ciqs(ATND) is null"); }
						atndCSV = CSVUtils.convertCIQToCSV(ciqs.get("ATND"), "eNodeB Ericsson", "ATND_ENODEB");
						if (CSVUtils.existsAndNotEmpty(atndCSV, false)) {
							List<String> headerKeys = new ArrayList<String>();
							headerKeys.add("eNodeB name");
							headerKeys.add("eNodeB ID");
							atndCSV = CSVUtils.filterNonHeaderRows(atndCSV, headerKeys);
							CSVUtils.setCIQCSVFile("ATND_ENODEB", atndCSV);
						}
					}
				}
			}
			File atnd5GMME = CSVUtils.convertCIQToCSV(ciqs.get("ATND"), TMOConstants.tmoATNDMmeFileNameRegex, "ATND_MME");
			if (CSVUtils.existsAndNotEmpty(atnd5GMME, false)) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("ipAddress1");
				headerKeys.add("ipAddress2");
				atndCSV = CSVUtils.filterNonHeaderRows(atnd5GMME, headerKeys);
				CSVUtils.setCIQCSVFile("ATND_MME", atnd5GMME);
			}

			// convert 5G TND to CSV
			File atnd5GCSV = CSVUtils.convertCIQToCSV(ciqs.get("ATND"), "gNodeB Ericsson", "ATND_GNODEB");
			if (CSVUtils.existsAndNotEmpty(atnd5GCSV, false)) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("gNodeB name");
				headerKeys.add("gNodeB ID");
				atndCSV = CSVUtils.filterNonHeaderRows(atnd5GCSV, headerKeys);
				CSVUtils.setCIQCSVFile("ATND_GNODEB", atnd5GCSV);
				
				// this is 5G
				has5GSites = true;
			}
			else {
				if (!CSVUtils.checkIfsheetExistsInExcel(new File(atndFile),"gNodeB Ericsson")) {
					atndFile = FileUtil.getFilePathFromFolder(inputDir, TMOConstants.tmo5GATNDFileNameRegex, false);
					if (!atndFile.isEmpty()) {
						ciqs.put("ATND", new File(atndFile));
						try {Logger.logger.debug("In 459 ciqs(ATND) is: " + ciqs.get("ATND").getAbsolutePath());}catch(Exception ex) {Logger.logger.debug("In 459 ciqs(ATND) is null"); }
						atnd5GCSV = CSVUtils.convertCIQToCSV(ciqs.get("ATND"), "gNodeB Ericsson", "ATND_GNODEB");
						if (CSVUtils.existsAndNotEmpty(atnd5GCSV, false)) {
							List<String> headerKeys = new ArrayList<String>();
							headerKeys.add("gNodeB name");
							headerKeys.add("gNodeB ID");
							atnd5GCSV = CSVUtils.filterNonHeaderRows(atnd5GCSV, headerKeys);
							CSVUtils.setCIQCSVFile("ATND_GNODEB", atnd5GCSV);

							// this is 5G
							has5GSites = true;
						}
					}
				}
			}

			// 01142021: convert New SCU TND to CSV
			if (ciqs.get("ATND") != null && ciqs.get("ATND").exists()) {
				if (!ciqs.get("ATND").getName().matches(TMOConstants.tmoScuATNDFileNameRegex)) {
					atndFile = FileUtil.getFilePathFromFolder(inputDir, ".*[Tt][Nn][Dd].*\\.(xls|xlsx|xlsm)$", false);
					ciqs.put("ATND", new File(atndFile));
					try {Logger.logger.debug("In 480 ciqs(ATND) is: " + ciqs.get("ATND").getAbsolutePath());}catch(Exception ex) {Logger.logger.debug("In 480 ciqs(ATND) is null"); }
				}
				File atndNewSCUCSV = CSVUtils.convertCIQToCSV(ciqs.get("ATND"), "Ericsson", "ATND_NEW_SCU");
				if (CSVUtils.existsAndNotEmpty(atndNewSCUCSV, false)) {
					List<String> headerKeys = new ArrayList<String>();
					headerKeys.add("Site ID");
					headerKeys.add("Node Name");
					atndCSV = CSVUtils.filterNonHeaderRows(atndNewSCUCSV, headerKeys);
					CSVUtils.setCIQCSVFile("ATND_NEW_SCU", atndNewSCUCSV);
				}
			}

			// 03052021: convert IPSec TND to CSV
			if (ciqs.get("ATND") != null && ciqs.get("ATND").exists()) {
				if (!ciqs.get("ATND").getName().matches(TMOConstants.tmoIPSecATNDFileNameRegex)) {
					atndFile = FileUtil.getFilePathFromFolder(inputDir, ".*[Tt][Nn][Dd].*\\.(xls|xlsx|xlsm)$", false);
					ciqs.put("ATND", new File(atndFile));
					try {Logger.logger.debug("In ciqs(ATND) is: " + ciqs.get("ATND").getAbsolutePath());}catch(Exception ex) {Logger.logger.debug("In ciqs(ATND) is null"); }
				}
				File atndIPSecCSV = CSVUtils.convertCIQToCSV(ciqs.get("ATND"), "SeGW IP Information", "ATND_IPSEC");
				if (CSVUtils.existsAndNotEmpty(atndIPSecCSV, false)) {
					List<String> headerKeys = new ArrayList<String>();
					headerKeys.add("ENM Server");
					atndCSV = CSVUtils.mergeHeaderRows(atndIPSecCSV, headerKeys);
					CSVUtils.setCIQCSVFile("ATND_IPSEC", atndIPSecCSV);
				}
			}

			// if data not available, stop process
			if (!CSVUtils.existsAndNotEmpty(CSVUtils.getCIQCSVFile("ATND_ENODEB"), false)) {
				if (!CSVUtils.existsAndNotEmpty(CSVUtils.getCIQCSVFile("ATND_GNODEB"), false)) {
					if (!CSVUtils.existsAndNotEmpty(CSVUtils.getCIQCSVFile("ATND_ENODEB_GNODEB"), false)) {
						if (ciqs.get("ATND") != null && ciqs.get("ATND").exists() && ciqs.get("ATND").getName().matches(TMOConstants.tmoScuATNDFileNameRegex)) {
							if (!CSVUtils.existsAndNotEmpty(CSVUtils.getCIQCSVFile("ATND_NEW_SCU"), false)) {
								Logger.getGmoLogger().printError("Unable to extract ATND data. Process stopped.");
								return false;
							}
						}
						else if (ciqs.get("ATND") != null && ciqs.get("ATND").exists() && ciqs.get("ATND").getName().matches(TMOConstants.tmoIPSecATNDFileNameRegex)) {
							if (!CSVUtils.existsAndNotEmpty(CSVUtils.getCIQCSVFile("ATND_IPSEC"), false)) {
								Logger.getGmoLogger().printError("Unable to extract ATND data. Process stopped.");
								return false;
							}
						}
						else {
							Logger.getGmoLogger().printError("Unable to extract ATND data. Process stopped.");
							return false;
						}
					}
					else {	// [06242020]
						has5GSites = true;
					}
				}
				else
				{
					// this is 5G
					has5GSites = true;
				}
			}

			Logger.getGmoLogger().printTextWithTimeStamp("Extracted data from local ATND file.");
		}
		catch (Exception e) {
			Logger.logger.error("initTNDData exception!", e);
			Logger.getGmoLogger().printError("Error initializing TND data! " + e.getMessage());
			return false;
		}
		return true;
	}

	/**
	 * Initialize KGET data
	 * @return true if successful, otherwise false
	 */
	public boolean initKGETData(String inputDir)
	{
		try {
			
			CSVUtils.getMOCToCSVFile().clear();
			// extract data from KGETs if existing
			ArrayList<String> kgetFiles = FileUtil.getFilePathsFromFolder(inputDir, ".*\\.([Ll][Oo][Gg]|[Tt][Xx][Tt])$", false);
			if (!kgetFiles.isEmpty()) {
				KgetUtil kgetUtil = new KgetUtil();
				kgetUtil.extractKgetToCsv(kgetFiles, CiqConstants.mocListForCSVLogic);
			}
			else {
				// [01262021] No need to parse Kgets if kget CSVs already exist, parsed by Multi-Du data collection
				ArrayList<String> kgetCsvFiles = FileUtil.getFilePathsFromFolder(FileUtil.getCmCiqDirectory(), "KGET_.*\\.csv$", false);
				if (!(kgetCsvFiles != null && !kgetCsvFiles.isEmpty())) {
					Logger.logger.info("Unable to locate KGET files in " + inputDir + ". Process stopped.");
					Logger.getGmoLogger().printTextWithTimeStamp("Unable to locate/parse KGET files in input directory.");		// [11102021]	For S2G or manual, in case kgets are not parsed
				}
				else {
					Logger.logger.info("Previously parsed KGET CSV files will be re-used.");
				}

				return false;
			}

			Logger.getGmoLogger().printTextWithTimeStamp("Extracted data from KGET files.");
		}
		catch (Exception e) {
			Logger.logger.error("initKGETData exception!", e);
			Logger.getGmoLogger().printError("Error initializing KGET data! " + e.getMessage());
			return false;
		}
		return true;
	}
	
	
	/**
	 * Initialize c2g inputs
	 * @return true if successful, otherwise false
	 */
	public boolean c2gExcaliburMongo() {
			
		try {
			
			//Transport 2g & 3g
			ciqs.put("TRANSPORT_2G_3G", new File(inputDir + File.separator + "TMobile_Excalibur_ATND_2G_3G_GENERATED.xlsx"));
			File atnd2GAnd3GCSV = CSVUtils.convertCIQToCSV(ciqs.get("TRANSPORT_2G_3G"), "transport", "transport");
			atnd2GAnd3GCSV = new C2GExcaliburMongo().getConvertedTransportFile(atnd2GAnd3GCSV);
		    List<String> lines = Files.readAllLines(atnd2GAnd3GCSV.toPath());
			if (lines.size() > 1) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("Site name");
				CSVUtils.setCIQCSVFile("ATND2G3G_C2G_Transport", atnd2GAnd3GCSV);
				has2GAnd3GSites = true;
			}
			
			// gsm 2g
			ciqs.put("GSM_2G", new File(inputDir + File.separator + "TMobile_Excalibur_GSM_GENERATED.xlsx"));
			
			File gsmCellCsv = CSVUtils.convertCIQToCSV(ciqs.get("GSM_2G"), "Cell", "Cell");
			gsmCellCsv = new C2GExcaliburMongo().getConvertedCellFile(gsmCellCsv);
			lines = Files.readAllLines(gsmCellCsv.toPath());
			if (lines.size() > 1) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("Site Name");
				//CSVUtils.setCIQCSVFile("GSM2G_CELL", gsmCellCsv);
				CSVUtils.setCIQCSVFile("GSM", gsmCellCsv);
				has2GAnd3GSites = true;
			}
			
			File gsmLossesAndDelaysCsv = CSVUtils.convertCIQToCSV(ciqs.get("GSM_2G"), "Losses And Delays", "Losses And Delays");
			gsmLossesAndDelaysCsv = new C2GExcaliburMongo().getConvertedLossesAndDelaysFile(gsmLossesAndDelaysCsv);
			lines = Files.readAllLines(gsmLossesAndDelaysCsv.toPath());
			if (lines.size() > 1) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("Site Name");
				CSVUtils.setCIQCSVFile("GSM2G_LossesAndDelays", gsmLossesAndDelaysCsv);
				has2GAnd3GSites = true;
			}
			
			/*
			 * File gsmDipDetailsCsv = CSVUtils.convertCIQToCSV(ciqs.get("GSM_2G"),
			 * "Dip_details", "Dip_details"); gsmDipDetailsCsv = new
			 * C2GExcaliburMongo().getConvertedDipDetailsFile(gsmDipDetailsCsv); if
			 * (CSVUtils.existsAndNotEmpty(gsmDipDetailsCsv, false)) { List<String>
			 * headerKeys = new ArrayList<String>(); headerKeys.add("Site Name");
			 * CSVUtils.setCIQCSVFile("GSM2G_DipDetails", gsmDipDetailsCsv); has2GAnd3GSites
			 * = true; }
			 */
			
			File gsmExtCellCsv = CSVUtils.convertCIQToCSV(ciqs.get("GSM_2G"), "GSM_ext_cell", "GSM_ext_cell");
			//gsmExtCellCsv = new C2GExcaliburMongo().getConvertedGsmCellFile(gsmExtCellCsv);
			lines = Files.readAllLines(gsmExtCellCsv.toPath());
			if (lines.size() > 1) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("Site Name");
				CSVUtils.setCIQCSVFile("GSM2G_GSMExtCell", gsmExtCellCsv);
				has2GAnd3GSites = true;
			}
			
			File gsmLteCsv = CSVUtils.convertCIQToCSV(ciqs.get("GSM_2G"), "GSM-LTE-Relation", "GSM-LTE-Relation");
			gsmLteCsv = new C2GExcaliburMongo().getConvertedGsmLte(gsmLteCsv);
			lines = Files.readAllLines(gsmLteCsv.toPath());
			if (lines.size() > 1) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("Site Name");
				CSVUtils.setCIQCSVFile("GSM2G_GSMLTERelation", gsmLteCsv);
				has2GAnd3GSites = true;
			}
			
			// wcdma 3g
			ciqs.put("WCDMA_3G", new File(inputDir + File.separator + "TMobile_Excalibur_WCDMA_GENERATED.xlsx"));
			
			File wcdmaClusterCsv = CSVUtils.convertCIQToCSV(ciqs.get("WCDMA_3G"), "cluster", "cluster");
			wcdmaClusterCsv = new C2GExcaliburMongo().getConvertedClusterFile(wcdmaClusterCsv);
			lines = Files.readAllLines(wcdmaClusterCsv.toPath());
			if (lines.size() > 1) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("Site");
				CSVUtils.setCIQCSVFile("WCDMA3G_Cluster", wcdmaClusterCsv);
				has2GAnd3GSites = true;
			}
			
			File wcdmaRbsSiteCsv = CSVUtils.convertCIQToCSV(ciqs.get("WCDMA_3G"), "rbsSite", "rbsSite");
			wcdmaRbsSiteCsv = new C2GExcaliburMongo().getConvertedRbsSiteFile(wcdmaRbsSiteCsv);
			lines = Files.readAllLines(wcdmaRbsSiteCsv.toPath());
			if (lines.size() > 1) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("siteId");
				CSVUtils.setCIQCSVFile("WCDMA3G_RbsSite", wcdmaRbsSiteCsv);
				has2GAnd3GSites = true;
			}
			
			File wcdmaDynRnCsv = CSVUtils.convertCIQToCSV(ciqs.get("WCDMA_3G"), "dynRn", "dynRn");
			wcdmaDynRnCsv = new C2GExcaliburMongo().getConvertedDynRnFile(wcdmaDynRnCsv);
			lines = Files.readAllLines(wcdmaDynRnCsv.toPath() , StandardCharsets.ISO_8859_1);
			if (lines.size() > 1) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("site Name");
				//CSVUtils.setCIQCSVFile("WCDMA3G_DynRn", wcdmaDynRnCsv);
				CSVUtils.setCIQCSVFile("WCDMA", wcdmaDynRnCsv);
				has2GAnd3GSites = true;
			}
			
			File wcdmaLacSacRacCsv = CSVUtils.convertCIQToCSV(ciqs.get("WCDMA_3G"), "lacSacRac", "lacSacRac");
			wcdmaLacSacRacCsv = new C2GExcaliburMongo().getConvertedLacSacRacFile(wcdmaLacSacRacCsv);
			lines = Files.readAllLines(wcdmaLacSacRacCsv.toPath());
			if (lines.size() > 1) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("site Name");
				CSVUtils.setCIQCSVFile("WCDMA3G_LacSacRac", wcdmaLacSacRacCsv);
				has2GAnd3GSites = true;
			}
			
			File UmtsLteCsv = CSVUtils.convertCIQToCSV(ciqs.get("WCDMA_3G"), "UMTS-LTE-RELATIONS", "UMTS-LTE-RELATIONS");
			UmtsLteCsv = new C2GExcaliburMongo().getConvertedWcdmaLte(UmtsLteCsv);
			lines = Files.readAllLines(UmtsLteCsv.toPath());
			if (lines.size() > 1) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("site Name");
				CSVUtils.setCIQCSVFile("WCDMA3G_UMTSLTERelations", UmtsLteCsv);
				has2GAnd3GSites = true;
			}
			
			if(has2GAnd3GSites)
				has2GSites = has3GSites = true;
				
		} catch (Exception e) {
			Logger.logger.error("initialize c2g inputs exception!", e);
			Logger.getGmoLogger().printError("Error initializing c2g inputs! " + e.getMessage());
			return false;
		}
		return true;
	}
	
	/**
	 * @deprecated
	 */
	public boolean initMongoData() {

		try {
			has2GSites = false;		// [02112021] Reset just to be sure value from prior GMO run is carried to next GMO run
			has3GSites = false;		// [02112021] Reset just to be sure value from prior GMO run is carried to next GMO run
			
			// Added by satwik - for 2g & 3g
			// Initialize Transport data from Mongo
			Mongo mongo = new Mongo(SystemConstants.MONGO_SERVER_PROD, SystemConstants.SSH_USER, SystemConstants.SSH_PW , SystemConstants.MONGO_DB_NAME, SystemConstants.MONGO_PORT,
					SystemConstants.MONGO_COLLECTION_NAME, true);
			sites = CommonUtil.getSiteListMatrixSet(siteList);
			ciqs.put("ATND2G_Transport", mongo.getCsvDirectory(sites, true));

			File atnd2GCSV = ciqs.get("ATND2G_Transport");
			if (CSVUtils.existsAndNotEmpty(atnd2GCSV, false)) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("BTS name");
				headerKeys.add("BTS ID");
				atnd2GCSV = CSVUtils.filterNonHeaderRows(atnd2GCSV, headerKeys);
				CSVUtils.setCIQCSVFile("ATND2G_Transport", atnd2GCSV);
				has2GSites = true;
			}

			ciqs.put("ATND3G_Transport", mongo.getCsvDirectory(sites, false));
			File atnd3GCSV = ciqs.get("ATND3G_Transport");
			if (CSVUtils.existsAndNotEmpty(atnd3GCSV, false)) {
				List<String> headerKeys = new ArrayList<String>();
				headerKeys.add("RBS name");
				headerKeys.add("RBS ID");
				atnd3GCSV = CSVUtils.filterNonHeaderRows(atnd3GCSV, headerKeys);
				CSVUtils.setCIQCSVFile("ATND3G_Transport", atnd3GCSV);
				has3GSites = true;
			}
			
			CSVUtils.setCIQCSVFile("WCDMA",  mongo.getWcdmaData(sites));
			CSVUtils.setCIQCSVFile("GSM", mongo.getGsmData(sites));


		} catch (Exception e) {
			Logger.logger.error("initMongoData exception!", e);
			Logger.getGmoLogger().printError("Error initializing mongo data!");
			return false;
		}
		return true;
	}

	/**
	 * Initialize SCU data
	 * @return true if successful, otherwise false
	 */
	public boolean initSCUData(String inputDir, HashMap<String, File> ciqs)
	{
		try {
			String scuInventoryFile = FileUtil.getFilePathFromFolder(inputDir, ".*T.*Mobile.*Other.*SCU.*[Ii]nventory.*\\.(xls|xlsx|xlsm)$", false);
			if (scuInventoryFile != null && !scuInventoryFile.isEmpty()) {
				ArrayList<String> scuInventoryFiles = FileUtil.getFilePathsFromFolder(inputDir, ".*SCU.*\\.(xls|xlsx|xlsm)$", false);
				for (String scuInventoryFilePath:scuInventoryFiles) {
					// cqMultiEnbCsv
					File scuInventoryCsv = CSVUtils.convertCIQToCSV(new File(scuInventoryFilePath), "SCU Invetory", "TMO_SCU_SCU_INVETORY");
					if (CSVUtils.existsAndNotEmpty(scuInventoryCsv, false)) {
						List<String> headerKeys = new ArrayList<String>();
						headerKeys.add("Site Name1");
						scuInventoryCsv = CSVUtils.mergeHeaderRows(scuInventoryCsv, headerKeys);
						CSVUtils.setCIQCSVFile("TMO_SCU_SCU_INVETORY", scuInventoryCsv);
						ciqs.put("EXISTING_SCU_DATA", new File(scuInventoryFilePath));
					}
				}
				Logger.getGmoLogger().printTextWithTimeStamp("Extracted data from SCU data file.");
			}
		}
		catch (Exception e) {
			Logger.logger.error("initSCUData exception!", e);
			Logger.getGmoLogger().printError("Error initializing data for existing SCU configuration! " + e.getMessage());
			return false;
		}
		return true;
	}
	
	/**
	 * Initialize Rilink Data for Physical and Logical DataPort mismatch
	 * @return true if successful, otherwise false
	 */
	public boolean initRilinkData(String inputDir, HashMap<String, File> ciqs)
	{
		try {
			String rilinkDataFile = FileUtil.getFilePathFromFolder(inputDir, TMOConstants.tmoPhysicalLogicalDataPortMismatch, false);
			if (rilinkDataFile != null && !rilinkDataFile.isEmpty()) {
				ArrayList<String> rilinkDataFiles = FileUtil.getFilePathsFromFolder(inputDir, TMOConstants.tmoPhysicalLogicalDataPortMismatch, false);
				for (String rilinkDataFilePath:rilinkDataFiles) {
					File rilinkCsv = CSVUtils.convertCIQToCSV(new File(rilinkDataFilePath), "RiLinks Audit", "TMO_PHYSICAL_LOGICAL_RILINK");
					if (CSVUtils.existsAndNotEmpty(rilinkCsv, false)) {
						CSVUtils.setCIQCSVFile("TMO_PHYSICAL_LOGICAL_RILINK", rilinkCsv);
						ciqs.put("TMO_PHYSICAL_LOGICAL_RILINK_DATA", new File(rilinkDataFilePath));
						hasDataPortMismatchSites = true;
					}
				}
				Logger.getGmoLogger().printTextWithTimeStamp("Extracted data from Rilink data file.");
			}
		}
		catch (Exception e) {
			Logger.logger.error("initRilinkData exception!", e);
			Logger.getGmoLogger().printError("Error initializing Rilink data for Physical and Logical Dataport Mismatch! " + e.getMessage());
			return false;
		}
		return true;
	}

	public void generate() throws Exception
	{
		try {
			if (tmoCCR != null) {
				
				if(hasDataPortMismatchSites) {
					generateCPRIRemappingScripts();
				}
				else {
					boolean is5GCarrierAdd = false;

					// ok you have one or more 5G sites
					// for now assume that all of them are 5G.
					// For the first one, check if it has a kget. If yes, that means they are all 2CC/4CC scope. So call the carrier add scripts method.
					for(Map.Entry<String, SiteCellObj> kvp : tmoCCR.getDUToDUInfo().entrySet())
					{
						SiteCellObj o1 = kvp.getValue();

						if(kvp.getValue().getgNodeBSectorCarrierMap() != null) {
							for(Map.Entry<String, GNodeBSectorCarrierObj> kvp2 : kvp.getValue().getgNodeBSectorCarrierMap().entrySet()) {
								is5GCarrierAdd = true;
								break;
							}
						}

						if(o1.is5G) {
							if(!o1.isNewSite) {
								is5GCarrierAdd = true;
							}
						}

						if(o1.isNewSite){
							o1.isecmcapable = true;
						}
					}

					parseNodeModelAndInitMIMData();
					
					boolean isHardStop = tmoDC.takeActionForMMBBPrechecksTest(sites);
					
					// small cell only
					if(hasExcaliburSmallCells && !isHardStop ) {
						generateSmallCellScripts();
					}
					else if(!isHardStop) {
						generateMixedModeBasebandScripts();      	//ExcaliburFdd
						
						generateTDDMixedModeBaseBandScripts(); 		//ExcaliburTDD
						
						generateMidbandMixedModeBasebandScripts();
						
						if(!hasExcalibur4G5G && !hasExcaliburSmallCells && !has2GAnd3GSites) {
							generateMixedModeBaseBandScriptsForNewConfig();

							generatedTddCarrierAddScripts();			// [12032021] GMO_TMO-206 N41 2C add to live node
						}
						
					}else {
						basicValidationOfOutput();
						return;
					}
					
					if(generateExcalibur && !hasExcaliburSmallCells) {
						if(has2GAnd3GSites) {
							generate2GAnd3GCarrierAddScripts();
						}
						generate5GCarrierAddScripts();
					}
					else if ((has2GSites || has3GSites || has2GAnd3GSites)) {
						generate2GAnd3GCarrierAddScripts();
					}else if(!hasExcaliburSmallCells) {
						generate5GCarrierAddScripts();
					}
					
					generateNSBScripts();
					//generateAnchorCabinet2Scripts();		// [01132021], [01272021] Moving to Multi-Du flow, for anchor, with similar, adjusted method.
					
					if (!has2GSites || !has3GSites || !has2GAnd3GSites) {
						generateCPRIRemappingScripts();
					}
					
					if(hasExcalibur4G5G || generateExcalibur) {
						generate2GAnd3GSCUScripts();
					}
					
					// TC_395 part 2
					generateNewSCUConfigurationScriptsForTest();
					
					if(!hasExcalibur4G5G && !hasExcaliburSmallCells && !has2GAnd3GSites) {
						TMO_CommonUtil.renameFolderForReconfig(sites, tmoCCR.getDUToDUInfo(), outputDir);
					}
					
					//[03252021] update to activate IPSec script generation from S2G
					generateIPSecScripts();

					boolean isCPRIRemappingProject = TMODataCollector.calculateTriggerForCPRIRemappingProject(tmoCCR.getDUToDUInfo(), sites, ciqs);
					boolean isSCUConfiguration = TMODataCollector.calculateTriggerForSCUConfiguration(tmoCCR.getDUToDUInfo(), sites, ciqs);
					boolean isIPSecConfiguration = TMODataCollector.calculateTriggerForIPSecConfiguration(tmoCCR.getDUToDUInfo(), sites, ciqs);
					boolean isB412CAddNSBOptionConfiguration = tmoDC.calculateTriggerForB412CAddNSBOptionConfiguration(tmoCCR.getDUToDUInfo(), sites, ciqs);
					//[11062020]- Do not generate if NSB Option is called from Multi-DU
					//[10252021]- Generate CSV from NSB option for B41-2C Add when called from Multi-DU scenario
					//GMO_TMO-148 B41 2C ADD Scope || Calling NSB Option from MultiDU Option
					boolean blnDoNotGenerateNSBOptionCalledFromMUltiDu = (!isMDUScope && !isCPRIRemappingProject && !isSCUConfiguration && !isIPSecConfiguration) 
							|| ((has2GSites || has3GSites || has2GAnd3GSites))
							|| (GlobalConst.isS2G && isMDUScope && isB412CAddNSBOptionConfiguration);
					if(blnDoNotGenerateNSBOptionCalledFromMUltiDu)
					{
						// Generate the SWInfoNew.csv file.
						generateSWInfoCSVFile();

						Boolean isEciScope = checkEciApplicableScope(siteList);	// Check to not zip EESI files unless for specific scopes (such as MMBB)
						
						generateEesiFiles();
						// [05292020] Refactored into method
						// [09112020] Removed server flags. Flags are handled in individual methods
						retrieveTmoLKFs();	
						
						if(generateExcalibur) {
							if(has2GSites || has3GSites || has2GAnd3GSites) {
								retrieve2gOSSNodeProtocol();
								generate2gRBSSummary();
							}
							
							retrieveOSSNodeProtocol();	// [06162020] Generic code to download required LKFs and store in EESI folders
							generateRBSSummary();	
						}
						else if(has2GSites || has3GSites || has2GAnd3GSites) {
							retrieve2gOSSNodeProtocol();
							generate2gRBSSummary();
						}
						else {
							
							retrieveOSSNodeProtocol();	// [06162020] Generic code to download required LKFs and store in EESI folders
							generateRBSSummary();		// [06162020] Generic code to download required LKFs and store in EESI folders
						}

						cleanFiles(outputDir);
						
						generateESIExcelSheet();
							
						// [05212021] New SRS logic to prevent out of memory error encountered with large RNDCIQs
						TMO_SRS_Generator srsGe= new TMO_SRS_Generator(inputDir,siteList,this);
						if( hasExcalibur4G5G) {
							if(isSiteInfoExists) {
								srsGe.processTmoSrsData();
							}
						}
						else {
							srsGe.processTmoSrsData();
						}
						
//						generateSRS();   //[08142020], [05242021] Removed: Old SRS process can cause out of memory error for very large RNDCIQs
						
						if(isEciScope || hasExcaliburSmallCells)
							zipIntegrationFolder(outputDir);	// [05292020] Refactored into method, moved from GmoExecuter
						
					}
					basicValidationOfOutput();	// [05262020] Refactored from generateNSBScripts 
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generate exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating! " + e.getMessage());
		}
	}

	

	private void generate2GAnd3GSCUScripts() {
		if(isSiteInfoExists) {
			ArrayList<String> physicalSites= CommonUtil.convertSiteListToArrayList(siteList);
			Set<String> newsites;
			if(generateExcalibur || hasExcalibur4G5G) {
				newsites =physicalSites.stream().collect(Collectors.toSet());
				TMOScuScripts tmoScuScripts = new TMOScuScripts(inputDir, siteList, outputDir, this);

				for (String site : newsites) {
					String sitename="";
					for(String sit: sites) {
						if((sit.contains(site) && !sit.equals(site))||hasExcaliburSmallCells) {
							sitename= sit;
							break;
						}
					}
					SiteCellObj duInfo = tmoCCR.getDUToDUInfo().get(sitename);
					String subnetwork = duInfo.subNetwork;

					ArrayList<HashMap<String, String>> fiveGRNDRowDataArray = CSVUtils
							.readDataRowArrayFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GNBINFO"), "gNB Name", sitename);
					ArrayList<HashMap<String, String>> Atnd = CSVUtils
							.readDataRowArrayFromCSVFile(CSVUtils.getCIQCSVFile("ATND_ENODEB"), "eNodeB name", sitename);
					String confType="";
					String cabinet ="";
					if (fiveGRNDRowDataArray != null && !fiveGRNDRowDataArray.isEmpty()) {
						//confType = fiveGRNDRowDataArray.get(0).get("ConfigurationType");
						cabinet = fiveGRNDRowDataArray.get(0).get("RBS type");
						if(cabinet.contains(" ")) {
							cabinet = cabinet.split(" ")[1];
						}
					}
					if(Atnd!= null && !Atnd.isEmpty()) {
						if(hasExcaliburSmallCells) {
							site = site + "2";
						}
						tmoScuScripts.generateExcaliburScuScripts(subnetwork,Atnd.get(0), site, outputDir,"DOS");
					}
					try {
						if(!hasExcaliburSmallCells) {
							File file = new File(outputDir + File.separator + "SCU");
							if(!file.exists()) {
								file.mkdir();
							}

							if(cabinet!=null && !cabinet.isEmpty() && cabinet.contains("6160")) {
								String ScuFileName="TMO_03_SCU_for_" + cabinet + "_PPC_generator_alarms_C" + site + ".xml";
								String ouputDir = file.toString();
								RemoteTemplate.getXLSFileFromServer("templates/lte/sector_add/tmobile/multidusectoradd/scu/" + "03_SCU_for_PPC_generator_alarms.xml", ouputDir + File.separator + ScuFileName, false);
							}
							else if(cabinet!=null && !cabinet.isEmpty() && cabinet.contains("6230")) {
								String ScuFileName="TMO_03_SCU_for_" + cabinet + "_PPC_generator_alarms_C" + site + ".xml";
								String ouputDir = file.toString();
								RemoteTemplate.getXLSFileFromServer("templates/lte/sector_add/tmobile/multidusectoradd/scu/" + "03_SCU_for_6230_PPC_generator_alarms.xml", ouputDir + File.separator + ScuFileName, false);
							}																									
							else{
								Logger.logger.error("Error generating the SCU_for_PPC_generator_alarms");
								Logger.getGmoLogger().printError("Error generating the SCU_for_PPC_generator_alarms");
							}
						}
					}
					catch(Exception e) {
						Logger.logger.error("Error generating the SCU_for_PPC_generator_alarms", e);
						Logger.getGmoLogger().printError("Error generating the SCU_for_PPC_generator_alarms" + e);
					}
				}
			}
		}
	}
	

	private void cleanFiles(String outputDir) {
		
		if(generateExcalibur) {
			String baseDirString=outputDir;
			File integrationDir = new File(outputDir + File.separator + "Integration" + File.separator + "ESI_Input");
			SiteCellObj duInfo =null;
			String siteDir="";
			for(String site : sites) {
				duInfo= tmoCCR.getDUToDUInfo().get(site);
				String upGradePackageName =  "".equalsIgnoreCase(duInfo.pciSiteObj.release) ? tmoDC.collectUpgradePackageReleaseFromKget(site) : duInfo.pciSiteObj.release;
				if(duInfo.has2GAnd3GSites) {

					String bbnsFile = baseDirString + File.separator + "01_" + duInfo.gsm2G.cellList.get(0).nodeName + "_BBNSB";
					baseDirString =bbnsFile + File.separator + duInfo.gsm2G.cellList.get(0).nodeName;
					File file = new File(baseDirString);
					for(File f : file.listFiles()) {
						String fName= f.getName();
						if(fName.startsWith("05_RN_GRAN_TMO") || 
								fName.endsWith("W_baseline_BBU_Baseline.mos") || fName.startsWith("05_RN_WRAN_TMO") || fName.startsWith("06_PTP_Slave_Configuration")) {
							f.delete();
						}
					}
					baseDirString=outputDir;
					String siteDir2g3g =outputDir + File.separator + duInfo.gsm2G.cellList.get(0).nodeName;
					File file2g3g = new File(siteDir2g3g);
					if(!file2g3g.exists()) {
						file2g3g.mkdir();
					}
					String bscFile =  outputDir + File.separator + "BSC";
					String rncFile =  outputDir + File.separator + "RNC";

					try {
						FileUtil.moveFolderToFolder(bbnsFile,siteDir2g3g);
						FileUtil.moveFolderToFolder(bscFile,siteDir2g3g);
						FileUtil.moveFolderToFolder(rncFile,siteDir2g3g);
					} catch (IOException e) {

					}
				}else if(duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
					siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + String.join("_", sites));
				}
				File toFile = new File(outputDir + File.separator + site);
				if(duInfo.tmoDUInfo.isExcalibur4G5GFDD && !duInfo.has2GAnd3GSites) {
					String deleteFileDir=integrationDir + File.separator + site + File.separator + site + File.separator + "Mobile_BBNSB_" + upGradePackageName;
					File file = new File(deleteFileDir);
					for(File f : file.listFiles()) {
						String fName= f.getName();
						if(fName.startsWith(site + "_E33") || 
								fName.startsWith(site + "_E34a") || fName.startsWith(site + "_E34b") || fName.startsWith(site + "_E37_RET_12_RET")) {
							f.delete();
						}
					}
					String endcFile =outputDir + File.separator + "03_ENDC";
					if (toFile.exists()) {
						try {
							if (duInfo.tmoDUInfo.isExcaliburSmallCellSite) {
								File endcFileDir = new File(endcFile);
								if (endcFileDir.isDirectory()) {
									File[] listFiles = endcFileDir.listFiles();
//									String copyPath = FileUtil.createDirReturnStr(
//											toFile.getAbsolutePath() + File.separatorChar + "03_ENDC"); 
									String SectorLevelGutranCellRelation = FileUtil.createDirReturnStr(
											toFile.getAbsolutePath() + File.separatorChar + "03_ENDC"
													+ File.separatorChar + "02_Sector_Level_Turnup_GutranCellRelation");
									String AfterRadioEnabledOneTime = FileUtil
											.createDirReturnStr(toFile.getAbsolutePath() + File.separatorChar
													+ "03_ENDC" + File.separatorChar + "01_After_Radio_Enabled_OneTime_"
													+ duInfo.duName);
									for (File f : listFiles) {
										if (f.getName().contains(duInfo.duName)) {
											if (f.getName().contains("Node_GutranCellRelation")) {
												Files.move(Paths.get(f.getAbsolutePath()),
														Paths.get(SectorLevelGutranCellRelation + File.separatorChar
																+ f.getName()),
														StandardCopyOption.REPLACE_EXISTING);
											} else {
												Files.move(Paths.get(f.getAbsolutePath()), Paths.get(
														AfterRadioEnabledOneTime + File.separatorChar + f.getName()),
														StandardCopyOption.REPLACE_EXISTING);
											}
										}
									}
								}

							} else if (duInfo.tmoDUInfo.isExcalibur4G5GFDD && hasExcalibur4G5G) {
								createEndcFolder(duInfo, toFile, endcFile);
							} else {
								FileUtil.moveFolderToFolder(endcFile, toFile.toString());
							}

						} catch (IOException e) {
						}
					}
					else {
						try {
							FileUtil.createDirectory(outputDir + File.separator + site);
							// move EndC files to site related.
							if(duInfo.tmoDUInfo.isExcalibur4G5GFDD && hasExcalibur4G5G) {
								createEndcFolder(duInfo, toFile, endcFile);
							
							}else {
							FileUtil.moveFolderToFolder(endcFile, toFile.toString());
							}
						} catch (IOException e) {
						}
					}
				}
				if((duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD) && !duInfo.has2GAnd3GSites) {
					File mvFile = new File(outputDir + File.separator + "01_" + site + "_BBNSB");

					File delFile = new File(outputDir + File.separator + site + File.separator + "CarrierAdd");

					if(toFile.exists()) {
						try {
							FileUtil.moveFolderToFolder(mvFile.toString(), toFile.toString());
						} catch (IOException e) {
						}
						FileUtil.deleteFolder(delFile);
					}
					else {
						try {
							FileUtil.createDirectory(outputDir + File.separator + site);
							FileUtil.moveFolderToFolder(mvFile.toString(), toFile.toString());
						} catch (IOException e) {
						}
					}
				}
			}
			boolean isConfig12 = sites.size() == 1 && sites.stream().findFirst().get().endsWith("2");
			if(hasExcalibur4G5G && !isConfig12) {
				FileUtil.deleteFolder(new File(siteDir));
			}
			if(hasExcalibur4G5G && isConfig12) {
				File file = new File(siteDir);
				for(File f : file.listFiles()) {
					if(!f.getName().endsWith("ENDC") && !f.getName().endsWith("BBNSB") 	) {
						FileUtil.deleteFolder(f);
					}
				} 
			}
			if(duInfo != null && (duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD)) {
				FileUtil.deleteFolder(new File(outputDir + File.separator + "BulkCarrierAdd"));
				FileUtil.deleteFolder(new File(outputDir + File.separator + "NGS"));
			}
			// small cell: delete the empty files
			if((duInfo.tmoDUInfo.isExcaliburSmallCellSite)||(hasExcalibur4G5G && !duInfo.tmoDUInfo.isExcaliburSmallCellSite)) {
				File endcFileDir = new File(outputDir + File.separatorChar + "03_ENDC"); 
				if (endcFileDir.listFiles().length ==0) {
					endcFileDir.delete();
				}
			}
		}
		else {
			String baseDirString=outputDir;
			File integrationDir = new File(outputDir + File.separator + "Integration" + File.separator + "ESI_Input");
			SiteCellObj duInfo =null;
			String siteDir="";
			for(String site : sites) {
				duInfo= tmoCCR.getDUToDUInfo().get(site);
				String upGradePackageName =  "".equalsIgnoreCase(duInfo.pciSiteObj.release) ? tmoDC.collectUpgradePackageReleaseFromKget(site) : duInfo.pciSiteObj.release;
				if(has2GSites || has3GSites || has2GAnd3GSites) {

					baseDirString =baseDirString + File.separator + "01_" + duInfo.gsm2G.cellList.get(0).nodeName + "_BBNSB" + File.separator + duInfo.gsm2G.cellList.get(0).nodeName;
					File file = new File(baseDirString);
					for(File f : file.listFiles()) {
						String fName= f.getName();
						if(fName.startsWith("05_RN_GRAN_TMO") || 
								fName.endsWith("W_baseline_BBU_Baseline.mos") || fName.startsWith("05_RN_WRAN_TMO") || fName.startsWith("06_PTP_Slave_Configuration")) {
							f.delete();
						}
					}
					baseDirString=outputDir;
				}else if(hasExcalibur4G5G) {
						siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + String.join("_", sites));
				}
				File toFile = new File(outputDir + File.separator + site);
				if(duInfo.tmoDUInfo.isExcalibur4G5GFDD) {
					String deleteFileDir=integrationDir + File.separator + site + File.separator + site + File.separator + "Mobile_BBNSB_" + upGradePackageName;
					File file = new File(deleteFileDir);
					for(File f : file.listFiles()) {
						String fName= f.getName();
						if(fName.startsWith(site + "_E33") || 
								fName.startsWith(site + "_E34a") || fName.startsWith(site + "_E34b") || fName.startsWith(site + "_E37_RET_12_RET")) {
							f.delete();
						}
					}
					String endcFile =outputDir + File.separator + "03_ENDC";
					if (toFile.exists()) {
						try {
							if (duInfo.tmoDUInfo.isExcaliburSmallCellSite) {
								File endcFileDir = new File(endcFile);
								if (endcFileDir.isDirectory()) {
									File[] listFiles = endcFileDir.listFiles();
//									String copyPath = FileUtil.createDirReturnStr(
//											toFile.getAbsolutePath() + File.separatorChar + "03_ENDC"); 
									 String SectorLevelGutranCellRelation = FileUtil.createDirReturnStr(
												toFile.getAbsolutePath() + File.separatorChar + "03_ENDC" + File.separatorChar + "02_Sector_Level_Turnup_GutranCellRelation");
									 String AfterRadioEnabledOneTime = FileUtil.createDirReturnStr(
												toFile.getAbsolutePath() + File.separatorChar + "03_ENDC" + File.separatorChar + "01_After_Radio_Enabled_OneTime_" + duInfo.duName);
									for (File f : listFiles) {
										if (f.getName().contains(duInfo.duName)) {
											if(f.getName().contains("Node_GutranCellRelation")) {
												Files.move(Paths.get(f.getAbsolutePath()), Paths.get(SectorLevelGutranCellRelation + File.separatorChar + f.getName()),
														StandardCopyOption.REPLACE_EXISTING);
											}else {
											Files.move(Paths.get(f.getAbsolutePath()), Paths.get(AfterRadioEnabledOneTime + File.separatorChar + f.getName()),
													StandardCopyOption.REPLACE_EXISTING);
											}
										}
									}
								}

							} else if (duInfo.tmoDUInfo.isExcalibur4G5GFDD && hasExcalibur4G5G) {
								createEndcFolder(duInfo, toFile, endcFile);
							}else {
								FileUtil.moveFolderToFolder(endcFile, toFile.toString());
							}

						} catch (IOException e) {
						}
					}
					else {
						try {
							FileUtil.createDirectory(outputDir + File.separator + site);
							 if (duInfo.tmoDUInfo.isExcalibur4G5GFDD && hasExcalibur4G5G) {
									createEndcFolder(duInfo, toFile, endcFile);
								}else {
									FileUtil.moveFolderToFolder(endcFile, toFile.toString());
								}
						} catch (IOException e) {
						}
					}

				}
				if(duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
					File mvFile = new File(outputDir + File.separator + "01_" + site + "_BBNSB");

					File delFile = new File(outputDir + File.separator + site + File.separator + "CarrierAdd");

					if(toFile.exists()) {
						try {
							FileUtil.moveFolderToFolder(mvFile.toString(), toFile.toString());
						} catch (IOException e) {
						}
						FileUtil.deleteFolder(delFile);
					}
					else {
						try {
							FileUtil.createDirectory(outputDir + File.separator + site);
							FileUtil.moveFolderToFolder(mvFile.toString(), toFile.toString());
						} catch (IOException e) {
						}
					}
				}
			}
			boolean isConfig12 = sites.size() == 1 && sites.stream().findFirst().get().endsWith("2");
			if(hasExcalibur4G5G && !isConfig12) {
				FileUtil.deleteFolder(new File(siteDir));
			}
			if(hasExcalibur4G5G && isConfig12) {
				File file = new File(siteDir);
				for(File f : file.listFiles()) {
					if(!f.getName().endsWith("ENDC") && !f.getName().endsWith("BBNSB") 	) {
						FileUtil.deleteFolder(f);
					}
				} 
			}
			if(duInfo != null && (duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD)) {
				FileUtil.deleteFolder(new File(outputDir + File.separator + "BulkCarrierAdd"));
				FileUtil.deleteFolder(new File(outputDir + File.separator + "NGS"));
			}
			// small cell: delete the empty files
			if((duInfo.tmoDUInfo.isExcaliburSmallCellSite)||(hasExcalibur4G5G && !duInfo.tmoDUInfo.isExcaliburSmallCellSite)) {
				File endcFileDir = new File(outputDir + File.separatorChar + "03_ENDC"); 
				if (endcFileDir.listFiles().length ==0) {
					endcFileDir.delete();
				}
			}
		}
	}

	private void createEndcFolder(SiteCellObj duInfo, File toFile, String endcFile) throws IOException {
		File endcFileDir = new File(endcFile);
		if (endcFileDir.isDirectory()) {
			File[] listFiles = endcFileDir.listFiles();
			String ENDC = FileUtil.createDirReturnStr(
					toFile.getAbsolutePath() + File.separatorChar + "03_ENDC");
			for (File f : listFiles) {
				if (f.getName().contains(duInfo.duName)) {
					Files.move(Paths.get(f.getAbsolutePath()),
							Paths.get(ENDC + File.separatorChar + f.getName()),
							StandardCopyOption.REPLACE_EXISTING);
					// FileUtil.moveFolderToFolder(endcFile, toFile.toString());
				}
			}
		}
	}

	private void generate2GAnd3GCarrierAddScripts() {
		SimpleDateFormat sdf = new SimpleDateFormat("yyyy_MM_dd'T'HH_mm_ss'Z'");
		String bscRelationsDirectory  =  outputDir + File.separator + "BSC";
		new File(bscRelationsDirectory).mkdirs();
		ArrayList<String> physicalSites= CommonUtil.convertSiteListToArrayList(siteList);
		Set<String> newsites;
		if(generateExcalibur) {
			newsites =physicalSites.stream().collect(Collectors.toSet());
		}
		else {
			newsites= sites;
		}
		for (String site : newsites) {
			SiteCellObj duInfo = tmoCCR.getDUToDUInfo().get(site);
			if (duInfo != null && (duInfo.has2Gsites || duInfo.has3Gsites || duInfo.has2GAnd3GSites)) {
				//Baseband
				String bbnsbPath =outputDir + File.separator + "01_" + duInfo.gsm2G.cellList.get(0).nodeName
						 + "_BBNSB" + File.separator + duInfo.gsm2G.cellList.get(0).nodeName;
				//String siteOutputDirectory = outputDir + File.separator + "Baseband";
				new File(bbnsbPath).mkdirs();
				//siteOutputDirectory =  siteOutputDirectory + File.separator + site;
				//new File(bbnsbPath).mkdirs();
				String ptpSlaveConfFileName = "06_PTP_Slave_Configuration_L20Q4.mos";
				generate2GPTPSlaveConfigurationScript(duInfo, bbnsbPath + File.separator + ptpSlaveConfFileName, "DOS");
				String granFileName ="05_RN_GRAN_TMO_G+W_NSB_Production_Tmobile_" + sdf.format(new Date())+ ".mos";
				generate2GAnd3GGRANScripts(duInfo, bbnsbPath + File.separator + granFileName, "DOS");
				String wranFileName ="05_RN_WRAN_TMO_G+W_NSB_Production_Tmobile_" + sdf.format(new Date())+ ".mos";
				generate2Gand3GWRANScripts(duInfo, bbnsbPath + File.separator + wranFileName, "DOS");
				WcdmaLteRelations(duInfo);
				generateRNC(duInfo,site,outputDir,"DOS");
				generateBscCellData(duInfo, bscRelationsDirectory);
				generateIntraSiteBscRelations(duInfo, bscRelationsDirectory + File.separator + "P1_1b_" + duInfo.gsm2G.cellList.get(0).rSite+ "_IntraSiteBscRelations.txt");
				generateExternalCellDeletion(duInfo,site, bscRelationsDirectory);
				XMLScripts.generateWcdmaRelation(duInfo,site,outputDir,"DOS");
			}
		}
		//generate2GTo2GIntraBscRelations(sites, bscRelationsDirectory);
	}
	
	private void generateExternalCellDeletion(SiteCellObj duInfo,String site,  String bscRelationsDirectory) {
		
		try {
			StringBuilder sb = new StringBuilder();
			sb.append("!***** GSM EXTERNAL DELETION DATA FOR " + site + " *****!" + eol + eol);
			
			if(duInfo.gsm2G!=null && duInfo.gsm2G.cellList!=null && !duInfo.gsm2G.cellList.isEmpty()) {
				sb.append("!!!! 2G to 2G !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol);
				for (GsmCell cell : duInfo.gsm2G.cellList) {
					sb.append("RLDEP:CELL=" + cell.name + ";" + eol);
				}
				sb.append("\n!!!!!!!!!!!!!IGNORE IF BELOW FAULT CODE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol
						+ "!!!!!!!!!!!!!<RLDEP:CELL=AT2492A;!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol
						+ "!!!!!!!!!!!!!NOT ACCEPTED!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol
						+ "!!!!!!!!!!!!!FAULT CODE 3!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol
						+ "!!!!!!!!!!!!!CELL NOT DEFINED!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol
						+ "!!!!!!!!!!!!!(0)CELL=AT2492A!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol + eol);

				for (GsmCell cell : duInfo.gsm2G.cellList) {
					sb.append("RLDEE:CELL=" + cell.name + ";" + eol);
				}
			}
			
			if(duInfo.wcdma3G!=null && duInfo.wcdma3G.cellList!=null && !duInfo.wcdma3G.cellList.isEmpty()) {
				sb.append("!!!! 2G to 3G !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol + eol);
				ArrayList<String> unchangedUtranCell = new ArrayList<>();
				List<WCDMACell>threeGCells = new LinkedList<WCDMACell>(duInfo.wcdma3G.cellList);
				for(WCDMACell cell:threeGCells) {
					unchangedUtranCell.add(cell.name);
					String tempName=cell.name.substring(2, 8);
					tempName=tempName+cell.name.charAt(9);

					cell.name=tempName;
				}
				sb.append("!Original UtranCellId-" + unchangedUtranCell.get(0) + "Truncated UtranCellId-" + threeGCells.get(0).name + eol + eol);
				for(WCDMACell cell:threeGCells) {
					sb.append("RLDEP:CELL=" + cell.name + ";" + eol);
				}
				sb.append("\n!!!!!!!!!!!!!IGNORE IF BELOW FAULT CODE!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol
						+ "!!!!!!!!!!!!!<RLDEP:CELL=AT2492A;!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol
						+ "!!!!!!!!!!!!!NOT ACCEPTED!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol
						+ "!!!!!!!!!!!!!FAULT CODE 3!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol
						+ "!!!!!!!!!!!!!CELL NOT DEFINED!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol
						+ "!!!!!!!!!!!!!(0)CELL=AT2492A!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol + eol);
				
				for(WCDMACell cell:threeGCells) {
					sb.append("RLDEE:CELL=" + cell.name + ";" + eol);
				}
				int count=0;
				for(String oriCell:unchangedUtranCell) {

					duInfo.wcdma3G.cellList.get(count).name=oriCell;
					count++;
				}
			}
			
			String fileName =  bscRelationsDirectory + File.separator + "P1_0_" + duInfo.gsm2G.cellList.get(0).bsc + "_" + duInfo.gsm2G.cellList.get(0).rSite + "_EXTERNAL CELLS_DELETE.txt";

			FileUtil.writeToFile(sb,fileName);
			
		}
		catch(Exception e) {
			Logger.logger.error("generateExternalCellDeletion Scripts exception!", e);
			Logger.getGmoLogger().printError("Error while generating ExternalCellDeletion!" + e.getMessage());
		}
	}

	private void generateRNC(SiteCellObj duInfo, String site, String fileName, String eolType) {
		if(duInfo.wcdma3G!=null && duInfo.wcdma3G.cellList!=null && !duInfo.wcdma3G.cellList.isEmpty()) {
			generateRNCUtranCellScript(duInfo, site, fileName, eolType);
			generateRNCIuLinkScript(duInfo, site, fileName, eolType);
		}

	}

	private void generateRNCIuLinkScript(SiteCellObj duInfo, String site, String fileName, String eolType) {
		String eol = StringUtil.getEOL(eolType);
		String fName  =  fileName + File.separator + "RNC" + File.separator + duInfo.wcdma3G.rncName + "_" + site + "_Iub" + ".mos";
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + fName);
		List<WCDMACell> cells = duInfo.wcdma3G.cellList;
		StringBuilder sb = new StringBuilder();
		try {
			
		sb.append(getNodeName(eol, duInfo));
		sb.append(getIubLink(eol, cells, site, duInfo));
		sb.append(getUserPlaneGbr(eol, duInfo));
		sb.append(getIubEdch(eol,duInfo));
		sb.append("gs-" + eol
				+ "confb-").append(eol).append(eol);
		File file = new File(fileName + File.separator + "RNC");
		if(!file.exists()) {
			file.mkdir();
		}
		
		FileUtil.writeToFile(sb, fName);
		}catch (Exception e) {
			Logger.logger.error("generateRNCIuLinkScript Scripts exception!", e);
			Logger.getGmoLogger().printError("Error while generating RNC Iublink script!" + e.getMessage());
		}
	}

	private Object getIubEdch(String eol, SiteCellObj duInfo) {
		StringBuilder sb = new StringBuilder();
		
		sb.append("pr ManagedElement=1,RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + ",IubEdch=1$").append(eol);
		sb.append("if $nr_of_mos = 0").append(eol);
		sb.append("crn RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + ",IubEdch=1").append(eol);
		sb.append("userLabel " + duInfo.wcdma3G.iubName).append(eol);
		sb.append("edchDataFrameDelayThreshold 60").append(eol);
		sb.append("end").append(eol).append("fi").append(eol);
		sb.append(eol);
		
		return sb.toString();
	}

	private Object getUserPlaneGbr(String eol, SiteCellObj duInfo) {
		StringBuilder sb = new StringBuilder();
		
		sb.append("pr ManagedElement=1,RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + "$").append(eol);
		sb.append("if $nr_of_mos = 1").append(eol);
		sb.append("set RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + " userPlaneGbrAdmBandwidthDl 1000" + eol
				+ "set RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + " userPlaneGbrAdmBandwidthUl 1000" + eol
				+ "set RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + " userPlaneGbrAdmEnabled 0" + eol
				+ "set RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + " userPlaneGbrAdmMarginDl 0" + eol
				+ "set RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + " userPlaneGbrAdmMarginUl 0" + eol
				+ "set RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + " softCongThreshGbrBwDl 100" + eol
				+ "set RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + " softCongThreshGbrBwUl 100").append(eol);
		sb.append("end").append(eol).append("fi").append(eol);
		sb.append(eol);
		
		return sb.toString();
	}

	private Object getIubLink(String eol, List<WCDMACell> cells, String site, SiteCellObj duInfo) {
		StringBuilder sb = new StringBuilder();
		sb.append("//  IubLink " + "U" + site).append(eol);
		sb.append(eol);
		
		sb.append("pr ManagedElement=1,RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + "$").append(eol);
		sb.append("if $nr_of_mos = 0").append(eol);
		sb.append("crn RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName).append(eol);
		sb.append("userLabel " + duInfo.wcdma3G.iubName).append(eol);
		sb.append("rbsId " + duInfo.wcdma3G.rbsId).append(eol);
		sb.append("dlHwAdm 99" + eol + "ulHwAdm 99" + eol + "controlPlaneTransportOption atm=0,ipv4=1" + eol
				+ "userPlaneTransportOption atm=0,ipv4=1" + eol
				+ "userPlaneIpResourceRef ManagedElement=1,IpSystem=1,IpAccessHostPool=IUB").append(eol);
		sb.append("remoteCpIpAddress1 " + duInfo.wcdma3G.iubIPAddress).append(eol);
		sb.append("end").append(eol).append("fi").append(eol);
		sb.append(eol);
		
		return sb.toString();
	}

	private void generateRNCUtranCellScript(SiteCellObj duInfo, String site, String fileName, String eolType) {

		String eol = StringUtil.getEOL(eolType);
		String file = fileName + File.separator + "RNC" + File.separator + duInfo.wcdma3G.rncName + "_" + site + "_UtranCell" + ".mos";
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		List<WCDMACell> cells = duInfo.wcdma3G.cellList;
		StringBuilder sb = new StringBuilder();
		sb.append(getNodeName(eol, duInfo));
		sb.append(getLocationArea(duInfo, site, eol));
		sb.append(eol);
		sb.append(getRoutingArea(duInfo, site, eol));
		sb.append(eol);

		try {
			sb.append(getServiceArea(duInfo, cells, site, eol));
			sb.append(eol);
			sb.append(getGsmVar(duInfo,eol));
			sb.append(eol);
			sb.append(getUltranCell(duInfo, cells, site, eol));
			sb.append(eol);
			sb.append(getRach(cells, eol));
			sb.append(eol);
			sb.append(getFach(cells, eol));
			sb.append(eol);
			sb.append(getPch(cells, eol));
			sb.append(eol);
			sb.append(getHsdsch(cells, eol));
			sb.append(eol);
			sb.append(getEul(cells, eol));
			sb.append(eol);
			sb.append("WAIT 60").append(eol);
			sb.append(eol);

			for (WCDMACell wcdmaCell : cells) {
				sb.append("set RncFunction=1,UtranCell=" + wcdmaCell.name + ",Hsdsch=1,Eul=1 administrativeState 1")
						.append(eol);
				sb.append(eol);
			}
			sb.append(eol);
			sb.append("// WcdmaCarrier block" + eol
					+ "$uarfcndl = " + cells.get(0).uarfcnDl + eol
					+ "mr varWCDMAcarrier" + eol
					+ "ma varWCDMAcarrier RncFunction=1,WcdmaCarrier= uarfcnDl $uarfcndl" + eol
					+ "if $nr_of_mos = 0" + eol
					+ "crn RncFunction=1,WcdmaCarrier=$uarfcndl" + eol
					+ "barredCnOperatorRef" + eol
					+ "defaultHoType 1" + eol);
			
			String freqband="";
			String sib5bisEnabled="";
			if(cells.get(0).name.startsWith("U")) {
				freqband="5";
				sib5bisEnabled="1";
			}
			else if(cells.get(0).name.startsWith("P")) {
				freqband="2";
				sib5bisEnabled="0";
			}
			sb.append("freqBand " + freqband + eol
					+ "sib5bisEnabled " + sib5bisEnabled + eol);
					
			sb.append("thresh2dRwrDrnc -90" + eol
					+ "uarfcnDl $uarfcndl" + eol
					+ "userLabel" + eol
					+ "end" + eol
					+ "fi" + eol
					+ "mr varWCDMAcarrier" + eol
					+ eol
					+ "mr varIurlink" + eol
					+ "ma varIurlink RncFunction=1,IurLink=" + eol
					+ "for $mo1 in varIurlink" + eol
					+ "$mordn =" + eol
					+ "$mocrn =" + eol
					+ "$mordn = rdn($mo1)" + eol
					+ "$mordn = $mordn,WcdmaCarrier=" + eol
					+ "mr varIWcdmaCarrier" + eol
					+ "ma varIWcdmaCarrier $mordn uarfcnDl $uarfcndl" + eol
					+ "if $nr_of_mos = 0" + eol
					+ "$mocrn = $mordn$uarfcndl" + eol
					+ "crn $mocrn" + eol
					+ "barredCnOperatorRef" + eol
					+ "defaultHoType 1" + eol
					+ "freqBand " + freqband + eol
					+ "sib5bisEnabled " + sib5bisEnabled + eol
					+ "thresh2dRwrDrnc -90" + eol
					+ "uarfcnDl $uarfcndl" + eol
					+ "userLabel" + eol
					+ "end" + eol
					+ "mr varIWcdmaCarrier" + eol
					+ "fi" + eol
					+ "done" + eol
					+ "mr varIurlink" + eol + eol);
			sb.append("confb-").append(eol);
			sb.append("gs-").append(eol);
			new File(fileName + File.separator + "RNC").mkdirs();
			FileUtil.writeToFile(sb, file);

		} catch (Exception e) {
			Logger.logger.error("generateRNCUtranCellScript Scripts exception!", e);
			Logger.getGmoLogger().printError("Error while generating RNC Ultracell script!" + e.getMessage());
		}
	}

	private String getGsmVar(SiteCellObj duInfo, String eol) {
		StringBuilder sb= new StringBuilder();
		String cgi=duInfo.gsm2G.cellList.get(0).cgi;
		String[] deli = cgi.split("-");
		sb.append("$gsmvariable =");
		sb.append(eol);
		sb.append("mr varexternalgsmnetwork1");
		sb.append(eol);
		sb.append("mr varexternalgsmnetwork2");
		sb.append(eol);
		sb.append("lma varexternalgsmnetwork1 ExternalGsmNetwork mcc " + deli[0]);
		sb.append(eol);
		sb.append("lma varexternalgsmnetwork2 varexternalgsmnetwork1 mnc " + deli[1]);
		sb.append(eol);
		sb.append("get varexternalgsmnetwork2 ExternalGsmNetworkId > $gsmvariable");
		sb.append(eol);
		sb.append("if $nr_of_mos = 0");
		sb.append(eol);
		sb.append("$gsmvariable = 1");
		sb.append(eol);
		sb.append("crn RncFunction=1,ExternalGsmNetwork=1");
		sb.append(eol);
		sb.append("mcc " + deli[0]);
		sb.append(eol);
		sb.append("mnc " + deli[1]);
		sb.append(eol);
		sb.append("mncLength 3");
		sb.append(eol);
		sb.append("userLabel");
		sb.append(eol);
		sb.append("end" + eol
				+ "//else " + eol
				+ "//get varexternalgsmnetwork2 ExternalGsmNetworkId > $gsmvariable" + eol
				+ "fi");
		sb.append(eol);
		sb.append("mr varexternalgsmnetwork1" + eol
				+ "mr varexternalgsmnetwork2");
		sb.append(eol);
		sb.append(eol);
		
		for(GsmCell gsmCell : duInfo.gsm2G.cellList) {
			
			String split[]=gsmCell.cgi.split("-");
			String fourthDelimiter="";
			String thirdDelimiter="";
			if(split.length>=4) {
				fourthDelimiter=split[3];
				thirdDelimiter=split[2];
			}
			sb.append("pr RncFunction=1,ExternalGsmNetwork=$gsmvariable,ExternalGsmCell=" + gsmCell.name + "$");
			sb.append(eol);
			
			sb.append("if $nr_of_mos = 0");
			sb.append(eol);
			sb.append("crn RncFunction=1,ExternalGsmNetwork=$gsmvariable,ExternalGsmCell=" + gsmCell.name);
			sb.append(eol);
			sb.append("bandIndicator 1 ");
			sb.append(eol);
			sb.append("bcc " + gsmCell.bcc);
			sb.append(eol);
			sb.append("bcchFrequency " + gsmCell.bcchno);
			sb.append(eol);
			sb.append("cellIdentity " + fourthDelimiter);
			sb.append(eol);
			sb.append("individualOffset 0");
			sb.append(eol);
			sb.append("lac " + thirdDelimiter);
			sb.append(eol);
			sb.append("maxTxPowerUl 100");
			sb.append(eol);
			sb.append("ncc " + gsmCell.ncc);
			sb.append(eol);
			sb.append("qRxLevMin -101");
			sb.append(eol);
			
			sb.append("userLabel");
			sb.append(eol);
			sb.append("end");
			sb.append(eol);
			sb.append("fi");
			sb.append(eol);
			sb.append(eol);
			
		}
		sb.append(getUraStr(duInfo,eol));
		sb.append(eol);
		
		return sb.toString();
	}

	private String getUraStr(SiteCellObj duInfo, String eol) {
		StringBuilder sb = new StringBuilder();
		ArrayList<WCDMACell> cells =duInfo.wcdma3G.cellList;
		Set<String> uraList = cells.stream().map( s -> s.UMTSURA1).distinct().collect(Collectors.toSet());
		String uraId=duInfo.wcdma3G.URAId;
		for(String ura : uraList) {
			sb.append("//URA DEFINITION ").append(eol);
			sb.append(eol);
			sb.append("pr RncFunction=1,Ura=" + ura);
			sb.append(eol);
			sb.append("if $nr_of_mos = 0");
			sb.append(eol);
			sb.append("crn RncFunction=1,Ura=" + ura);
			sb.append(eol);
			sb.append("uraIdentity " + uraId);
			sb.append(eol);
			sb.append("userLabel");
			sb.append(eol);
			sb.append("end");
			sb.append(eol);
			sb.append("fi");
			sb.append(eol);
		}

		return sb.toString();
	}

	private Object getNodeName(String eol, SiteCellObj duInfo) {
		StringBuilder sb = new StringBuilder();
		sb.append("confb+").append(eol);
		sb.append("gs+").append(eol);
		sb.append(eol);
		sb.append(eol);
		sb.append("get . logicalName > $Nodename").append(eol);
		sb.append("lt all").append(eol);
		sb.append("if $Nodename != " + duInfo.wcdma3G.rncName).append(eol);
		sb.append(
				"print Exiting !!!!!!!!!! ABORT due to Wrong Node, or OAM IP address mismatch, or Node Name mismatch etc. !!!!!!!!!!")
				.append(eol);
		sb.append("return").append(eol);
		sb.append("else").append(eol);
		sb.append("alt").append(eol);
		sb.append("fi").append(eol);
		sb.append(eol);

		return sb.toString();
	}

	private String getUltranCell(SiteCellObj duInfo, List<WCDMACell> cells, String site, String eol) {
		StringBuilder sb = new StringBuilder();
		for (WCDMACell wcdmaCell : cells) {

			sb.append("// UtranCell").append(eol);
			sb.append(eol);
			sb.append("pr ManagedElement=1,RncFunction=1,UtranCell=" + wcdmaCell.name + "$").append(eol);
			sb.append("if $nr_of_mos = 0").append(eol);
			sb.append("crn RncFunction=1,UtranCell=" + wcdmaCell.name).append(eol);
			sb.append(
					"absPrioCellRes cellReselectionPriority=3,sPrioritySearch1=62,sPrioritySearch2=7,threshServingLow=16,measIndFach=0")
					.append(eol);
			sb.append("anrIafUtranCellConfig anrEnabled=1,relationAddEnabled=1").append(eol);
			sb.append("userLabel " + wcdmaCell.name + eol);
			sb.append("localCellId " + wcdmaCell.cellIdentity + eol + "cId " + wcdmaCell.cellIdentity + eol);
			sb.append("cellBroadcastSac " + wcdmaCell.UMTSSAC + " " + eol);
			sb.append("cbsSchedulePeriodLength 16" + eol + "ctchOccasionPeriod 255" + eol);
			sb.append("tCell " + wcdmaCell.tCell + eol + "uarfcnUl " + wcdmaCell.uarfcnUl + eol + "uarfcnDl "
					+ wcdmaCell.uarfcnDl + eol + "primaryScramblingCode " + wcdmaCell.scramblingCode + eol
					+ "sib1PlmnScopeValueTag " + wcdmaCell.sib1PlmnScopeValueTag + eol
					+ "directedRetryTarget RncFunction=1," + wcdmaCell.directedRetryTarget + eol
					+ "maximumTransmissionPower " + wcdmaCell.maximumTransmissionPower + eol + "primaryCpichPower "
					+ wcdmaCell.primaryCpichPower + eol);
			sb.append("locationAreaRef RncFunction=1,LocationArea=" + duInfo.wcdma3G.UMTSLAC
					+ eol + "serviceAreaRef RncFunction=1,LocationArea="
					+ duInfo.wcdma3G.UMTSLAC + ",ServiceArea=" + wcdmaCell.UMTSSAC + "	" + eol
					+ "routingAreaRef RncFunction=1,LocationArea=" + duInfo.wcdma3G.UMTSLAC
					+ ",RoutingArea=" + duInfo.wcdma3G.UMTSRAC + "		" + eol
					+ "iubLinkRef RncFunction=1,IubLink=" + duInfo.wcdma3G.iubName + "	" + eol);
			sb.append("agpsEnabled 0" + eol + "aseDlAdm 500" + eol + "aseUlAdm 500" + eol + "dlCodeAdm 80" + eol
					+ "eulServingCellUsersAdm 25" + eol + "eulNonServingCellUsersAdm 42" + eol
					+ "eulServingCellUsersAdmTti2 8" + eol + "fachMeasOccaCycLenCoeff 3" + eol 
					+ "hsdpaUsersAdm 86" + eol + "hoType " + wcdmaCell.hoType + eol + "iflsMode 2" + eol
					+ "interFreqFddMeasIndicator 0" + eol + "individualOffset 0" + eol + "interPwrMax 30" + eol
					+ "loadSharingMargin 15" + eol + "loadSharingGsmFraction 100" + eol + "loadSharingGsmThreshold 99" + eol
					+ "minPwrMax -10" + eol + "minPwrRl -150" + eol + "pwrAdm 85" + eol + "pathlossThreshold 148" + eol
					+ "qHyst1 2" + eol + "qHyst2 2" + eol + "qQualMin -18" + eol + "qRxLevMin " + wcdmaCell.qRxLevMin + eol
					+ "qualMeasQuantity " + wcdmaCell.qualMeasQuantity + eol
					+ "releaseRedirect 1" + eol + "releaseRedirectEutraTriggers " + "csFallbackCsRelease=1,"
					+ "csFallbackDchToFach=0," + "dchToFach=0," + "fachToUra=0," + "fastDormancy=0,"
					+ "normalRelease=0" + eol + "servDiffRrcAdmHighPrioProfile 2" + eol + "sf4AdmUl 0" + eol + "sf8Adm 0" + eol
					+ "sf8AdmUl 2" + eol + "sf8gAdmUl 0" + eol + "sf16Adm 4" + eol + "sf16AdmUl 50" + eol + "sf16gAdm 0" + eol
					+ "sf32Adm 12" + eol + "sHcsRat -1" + eol + "sRatSearch 0" + eol + "sInterSearch 25" + eol
					+ "sIntraSearch 22" + eol + "treSelection 1" + eol + "usedFreqThresh2dEcno "
					+ wcdmaCell.usedFreqThresh2dEcno + eol + "usedFreqThresh2dRscp " + wcdmaCell.usedFreqThresh2dRscp
					+ eol + "hsIflsMarginUsers 0" + eol + "hsIflsThreshUsers 20" + eol + "rrcLcEnabled 1" + eol
					+ "uraRef RncFunction=1,Ura=" + wcdmaCell.UMTSURA1 + eol + "cellReserved 0" + eol
					+ "interRate 1590" + eol + "maxPwrMax 30" + eol + "minimumRate 370" + eol + "amrNbSelector 1" + eol);
			sb.append("end").append(eol);
			sb.append("fi").append(eol);
			sb.append(eol);
		}

		return sb.toString();
	}

	private String getServiceArea(SiteCellObj duInfo, List<WCDMACell> cells, String site, String eol) {
		StringBuilder sb = new StringBuilder();
		for (WCDMACell wcdmaCell : cells) {
			sb.append("// ServiceArea").append(eol);
			sb.append(eol);
			sb.append("pr ManagedElement=1,RncFunction=1,LocationArea=" + duInfo.wcdma3G.UMTSLAC + ",ServiceArea="
					+ wcdmaCell.UMTSSAC + "$").append(eol);
			sb.append("if $nr_of_mos = 0").append(eol);
			sb.append("crn RncFunction=1,LocationArea=" + duInfo.wcdma3G.UMTSLAC + ",ServiceArea=" + wcdmaCell.UMTSSAC)
					.append(eol);
			sb.append("userLabel " + wcdmaCell.UMTSSAC).append(eol);
			sb.append("sac " + wcdmaCell.UMTSSAC).append(eol);
			sb.append("end").append(eol);
			sb.append("fi").append(eol);
			sb.append(eol);
		}
		return sb.toString();

	}

	private String getRach(List<WCDMACell> cells, String eol) {
		StringBuilder sb = new StringBuilder();
		for (WCDMACell wcdmaCell : cells) {
			sb.append("// Rach").append(eol);
			sb.append(eol);
			sb.append("pr ManagedElement=1,RncFunction=1,UtranCell=" + wcdmaCell.name + ",Rach=1$").append(eol);
			sb.append("if $nr_of_mos = 0").append(eol);
			sb.append("crn RncFunction=1,UtranCell=" + wcdmaCell.name + ",Rach=1").append(eol);
			sb.append("userLabel 1" + eol + "preambleSignatures 65535" + eol + "subChannelNo 4095" + eol
					+ "aichPower -7" + eol + "maxPreambleCycle 8" + eol + "powerOffsetP0 2" + eol
					+ "powerOffsetPpm -4" + eol + "preambleRetransMax 32" + eol + "spreadingFactor 32" + eol
					+ "end" + eol + "fi");
			sb.append(eol);
		}
		return sb.toString();
	}

	private String getFach(List<WCDMACell> cells, String eol) {
		StringBuilder sb = new StringBuilder();
		for (WCDMACell wcdmaCell : cells) {

			sb.append("// Fach").append(eol);
			sb.append(eol);
			sb.append("pr ManagedElement=1,RncFunction=1,UtranCell=" + wcdmaCell.name + ",Fach=1$").append(eol);
			sb.append("if $nr_of_mos = 0").append(eol);
			sb.append("crn RncFunction=1,UtranCell=" + wcdmaCell.name + ",Fach=1").append(eol);
			sb.append("userLabel 1" + eol + "maxFach1Power 40" + eol + "end" + eol + "fi");
			sb.append(eol);
		}
		return sb.toString();
	}

	private String getPch(List<WCDMACell> cells, String eol) {
		StringBuilder sb = new StringBuilder();
		for (WCDMACell wcdmaCell : cells) {

			sb.append("// Pch").append(eol);
			sb.append(eol);
			sb.append("pr ManagedElement=1,RncFunction=1,UtranCell=" + wcdmaCell.name + ",Pch=1$").append(eol);
			sb.append("if $nr_of_mos = 0").append(eol);
			sb.append("crn RncFunction=1,UtranCell=" + wcdmaCell.name + ",Pch=1").append(eol);
			sb.append("userLabel 1" + eol + "end" + eol + "fi");
			sb.append(eol);
		}
		return sb.toString();

	}

	private String getHsdsch(List<WCDMACell> cells, String eol) {
		StringBuilder sb = new StringBuilder();
		for (WCDMACell wcdmaCell : cells) {

			sb.append("// Hsdsch").append(eol);
			sb.append(eol);
			sb.append("pr ManagedElement=1,RncFunction=1,UtranCell=" + wcdmaCell.name + ",Hsdsch=1$").append(eol);
			sb.append("if $nr_of_mos = 0").append(eol);
			sb.append("crn RncFunction=1,UtranCell=" + wcdmaCell.name + ",Hsdsch=1").append(eol);
			sb.append("userLabel 1" + eol + "numHsPdschCodes 1" + eol + "numHsScchCodes 3" + eol + "codeThresholdPdu656 0" + eol
					+ "deltaAck1 6" + eol + "deltaNack1 6" + eol + "deltaAck2 8" + eol + "deltaNack2 8" + eol
					+ "deltaCqi1 5" + eol + "deltaCqi2 7" + eol + "initialCqiRepetitionFactor 1" + eol
					+ "initialAckNackRepetitionFactor 1" + eol + "cqiFeedbackCycle 8" + eol
					+ "hsMeasurementPowerOffset 80" + eol + "end" + eol + "fi");
			sb.append(eol);
			sb.append(eol);
		}
		return sb.toString();

	}

	private String getEul(List<WCDMACell> cells, String eol) {
		StringBuilder sb = new StringBuilder();
		for (WCDMACell wcdmaCell : cells) {
			sb.append("// Eul").append(eol);
			sb.append(eol);
			sb.append("pr ManagedElement=1,RncFunction=1,UtranCell=" + wcdmaCell.name + ",Hsdsch=1,Eul=1$").append(eol);
			sb.append("if $nr_of_mos = 0").append(eol);
			sb.append("crn RncFunction=1,UtranCell=" + wcdmaCell.name + ",Hsdsch=1,Eul=1").append(eol);
			sb.append("userLabel 1" + eol + "eulMaxTargetRtwp -499" + eol + "numEhichErgchCodes 2" + eol
					+ "numEagchCodes 1" + eol + "end" + eol + "fi");
			sb.append(eol);
			sb.append(eol);
		}
		return sb.toString();

	}

	private String getRoutingArea(SiteCellObj duInfo, String site, String eol) {
		StringBuilder sb = new StringBuilder();
		sb.append("// RoutingArea").append(eol);
		sb.append(eol);
		sb.append("pr ManagedElement=1,RncFunction=1,LocationArea=" + duInfo.wcdma3G.UMTSLAC + ",RoutingArea="
				+ duInfo.wcdma3G.UMTSRAC + "$").append(eol);
		sb.append("if $nr_of_mos = 0").append(eol);
		sb.append("crn RncFunction=1,LocationArea=" + duInfo.wcdma3G.UMTSLAC + ",RoutingArea=" + duInfo.wcdma3G.UMTSRAC)
				.append(eol);
		sb.append("userLabel " + duInfo.wcdma3G.UMTSRAC).append(eol);
		sb.append("rac " + duInfo.wcdma3G.UMTSRAC).append(eol);
		sb.append("end").append(eol);
		sb.append("fi").append(eol);
		return sb.toString();
	}

	private String getLocationArea(SiteCellObj duInfo, String site, String eol) {
		StringBuilder sb = new StringBuilder();
		sb.append("// LocationArea").append(eol);
		sb.append(eol);
		sb.append("pr ManagedElement=1,RncFunction=1,LocationArea=" + duInfo.wcdma3G.UMTSLAC + "$").append(eol);
		sb.append("if $nr_of_mos = 0").append(eol);
		sb.append("crn RncFunction=1,LocationArea=" + duInfo.wcdma3G.UMTSLAC).append(eol);
		sb.append("userLabel " + duInfo.wcdma3G.UMTSLAC).append(eol);
		sb.append("lac " + duInfo.wcdma3G.UMTSLAC).append(eol);
		sb.append("end").append(eol);
		sb.append("fi").append(eol);
		return sb.toString();
	}
	
	
	private void generate2GTo2GIntraBscRelations(Set<String> sites, String outputDir) {
		String fileName = outputDir + File.separator + "Intra_BSC_Relations.txt";
		StringBuilder builder = new StringBuilder();
		List<GsmCell> twoGCells = new LinkedList<>();
		if(sites.size() <= 1 ) return;
		for (String site : sites) {
			SiteCellObj duInfo = tmoCCR.getDUToDUInfo().get(site);
			twoGCells.addAll(duInfo.gsm2G.cellList);
		}

		for (GsmCell cell : twoGCells) {
			for (GsmCell anotherCell : twoGCells) {
				if (!cell.name.equals(anotherCell.name)) {
					builder.append("RLNRI:CELL=" + cell.name + ", CELLR=" + anotherCell.name + ";" + eol);
					builder.append("RLNRC:CELL=" + cell.name + ", CELLR=" + anotherCell.name + ", CS=NO, CAND=BOTH, KHYST=6, KOFFSETP=0, LHYST=6, LOFFSETP=0, TRHYST=2, TROFFSETP=0;" + eol);
					builder.append("RLNRC:CELL=" + cell.name + ", CELLR=" + anotherCell.name + ", HIHYST=5, LOHYST=3, AWOFFSET=0, BQOFFSET=2, BQOFFSETAFR=2;" + eol);
				}
			}
		}
		FileUtil.writeToFile(builder, fileName);
	}

	private void generateIntraSiteBscRelations(SiteCellObj duInfo, String fileName) {

		try {
			
			if(duInfo.gsm2G.cellList.size() <= 1) return;
			StringBuilder sb = new StringBuilder();
			Collections.sort(duInfo.gsm2G.cellList, new Comparator<GsmCell>() {

				@Override
				public int compare(GsmCell o1, GsmCell o2) {
					return o1.name.compareTo(o2.name);
				}

			});

			sb.append("!****************************************************************!" + eol);
			sb.append("!******************* GSM NEIGHBOUR RELATION DATA ****************!" + eol);
			sb.append("!****************************************************************!" + eol);
			sb.append("!*  PROJECT NAME  :  T-Mobile *!                                  " + eol);
			sb.append("!*  BSC: " + duInfo.gsm2G.cellList.get(0).bsc + " *!                                              " + eol);
			sb.append("!*  PREPARED BY   :  " + CommonUtil.userName() + " *!                                  " + eol);
			sb.append("!----------------------------------------------------------------!" + eol);
			sb.append("!*  REVISION    :   A                                           *!" + eol); 
			sb.append("!----------------------------------------------------------------!" + eol);
			sb.append("!*--------------------------------------------------------------*!" + eol);
			sb.append("!*- KINDLY IGNORE THE FAULT CODE 32 : RELATION ALREADY EXISTS --*!" + eol);
			sb.append("!*--------------------------------------------------------------*!" + eol);
			sb.append("! NOTE:KINDLY CHECK & CONFIRM BEFORE DELETING THE NEIGHBOUR CELL !" + eol);
			sb.append("!****************************************************************!" + eol);
			sb.append("!***** GSM NEIGHBOUR DEFINITION & DELETION DATA FOR " + duInfo.duName + " *****!" + eol); 
			sb.append("!****************************************************************!" + eol);

			// Relations Between 2g - 2g cells
			sb.append("!!!! 2G to 2G !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol + eol);
			

			for (GsmCell cell : duInfo.gsm2G.cellList) {
				for (GsmCell anotherCell : duInfo.gsm2G.cellList) {
					if (!cell.name.equals(anotherCell.name)) {
						sb.append("RLNRI:CELL=" + cell.name + ", CELLR=" + anotherCell.name + ";" + eol);  //Excalibur_215 //revert back
						sb.append("RLNRC:CELL=" + cell.name + ", CELLR=" + anotherCell.name + ", CS=NO, CAND=BOTH, KHYST=3, KOFFSETP=0, LHYST=3, LOFFSETP=0, TRHYST=2, TROFFSETP=0;" + eol);
						sb.append("RLNRC:CELL=" + cell.name + ", CELLR=" + anotherCell.name + ", HIHYST=5, LOHYST=3, AWOFFSET=5, BQOFFSET=3, BQOFFSETAFR=3;" + eol);
					}
				}
			}
			
			sb.append(eol);
			sb.append(eol);
			ArrayList<String> unchangedUtranCell = new ArrayList<>();
			if(duInfo.wcdma3G!=null && duInfo.wcdma3G.cellList!=null && !duInfo.wcdma3G.cellList.isEmpty()) {
				sb.append("!!!! 2G to 3G !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol);

				List<WCDMACell> threeGCells;
				
				//List<WCDMACell> threeGCellsOriginal = new LinkedList<WCDMACell>(duInfo.wcdma3G.cellList);

				threeGCells = new LinkedList<WCDMACell>(duInfo.wcdma3G.cellList);
				for(WCDMACell cell:threeGCells) {
					unchangedUtranCell.add(cell.name);
					String tempName=cell.name.substring(2, 8);
					tempName=tempName+cell.name.charAt(9);

					cell.name=tempName;
				}
				sb.append("!Original UtranCellId-" + unchangedUtranCell.get(0) + "Truncated UtranCellId-" + threeGCells.get(0).name + eol);
				for(WCDMACell cell:threeGCells) {
					sb.append("RLDEI:CELL=" + cell.name + ", EXT, UTRAN;" + eol);
				}
				sb.append(eol);
				sb.append("!RNC ID " + duInfo.wcdma3G.rncId + "!" + eol);
				for(WCDMACell cell:threeGCells) {
					sb.append("RLDEC:CELL=" + cell.name + ", UTRANID=310-260-" + cell.UMTSLAC + "-" + cell.cellIdentity + "-" + duInfo.wcdma3G.rncId + ",FDDARFCN=" + cell.uarfcnDl + ",SCRCODE=" + cell.scramblingCode + ",MRSL=30;" + eol);
				}
				sb.append(eol);
				for(int i=0;i<threeGCells.size();i++) {
					sb.append("RLUMC:CELL=" + duInfo.gsm2G.cellList.get(i).name + ",ADD,UMFI=" + threeGCells.get(i).uarfcnDl + "-" + threeGCells.get(i).scramblingCode + "-NODIV,LISTTYPE=IDLE;" + eol);
				}
				sb.append(eol);
				for(int i=0;i<threeGCells.size();i++) {
					sb.append("RLUMC:CELL=" + duInfo.gsm2G.cellList.get(i).name + ",ADD,UMFI=" + threeGCells.get(i).uarfcnDl + "-" + threeGCells.get(i).scramblingCode + "-NODIV,LISTTYPE=ACTIVE;" + eol);
				}
				sb.append(eol);

				for(GsmCell cell : duInfo.gsm2G.cellList) {

					for(WCDMACell anothercell:threeGCells) {
						sb.append("RLNRI:CELL=" + cell.name + ",CELLR=" + anothercell.name + ",SINGLE;" + eol);
					}
				}
				sb.append(eol);


				for(GsmCell cell : duInfo.gsm2G.cellList) {
					
					sb.append("RLSUC:CELL=" + cell.name + ",SPRIO=YES,FDDREPTHR2=0,FDDMRR=0,FDDQMIN=6,FDDQOFF=0,QSC=15,QSCI=1,QSI=7;" + eol);	
				}
				sb.append(eol);
				sb.append("!!RAEPC:PROP=COEXUMTS-4;!!" + eol);

				for(int i=0;i<threeGCells.size();i++) {
					sb.append("RLSRC:CELL=" + duInfo.gsm2G.cellList.get(i).name + ",FDDARFCN=" + threeGCells.get(i).uarfcnDl + ",RATPRIO=3,HPRIOTHR=0,LPRIOTHR=9,QRXLEVMINU=0;" + eol);
				}
				sb.append(eol);
				sb.append(eol);
				sb.append(eol);
			}
		
			
			if(!hasExcalibur4G5G || generateExcalibur) {
				sb.append("!!!! 2G to 4G !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!" + eol);

				ArrayList<String> earfcnMap = CSVUtils
						.readDataArrayFromCSVFile(CSVUtils.getCIQCSVFile("GSM2G_GSMLTERelation"), "CELL_GSM", duInfo.gsm2G.cellList.get(0).name,"EARFCN",true);
				for(GsmCell cell : duInfo.gsm2G.cellList) {
					for(String earfcn:earfcnMap) {
						if(Integer.parseInt(earfcn)<65535)
							sb.append("RLEFC:CELL=" + cell.name + ",ADD,EARFCN=" + earfcn + ";" + eol);
					}
					sb.append(eol);
				}
				for(GsmCell cell : duInfo.gsm2G.cellList) {
					sb.append("RLSRC:CELL=" + cell.name + ",RATPRIO=0;" + eol);
				}
				sb.append(eol);


				for(GsmCell cell : duInfo.gsm2G.cellList) {
					for(String earfcn:earfcnMap) {
						if(Integer.parseInt(earfcn)<65535)
							sb.append("RLESC:CELL=" + cell.name + ",EARFCN=" + earfcn + ",MINCHBW=0;" + eol);
					}
					sb.append(eol);
				}

				for(GsmCell cell : duInfo.gsm2G.cellList) {
					for(String earfcn:earfcnMap) {
						if(Integer.parseInt(earfcn)<65535)
							sb.append("RLSRC:CELL=" + cell.name + ",EARFCN=" + earfcn + ",RATPRIO=6,HPRIOTHR=0,QRXLEVMINE=8,LPRIOTHR=9;" + eol);
					}
					sb.append(eol);
				}
			}

			sb.append("!****************************** EOF **********************************!");
			int count=0;
			if(duInfo.wcdma3G!=null && duInfo.wcdma3G.cellList!=null && !duInfo.wcdma3G.cellList.isEmpty()) {
				for(String oriCell:unchangedUtranCell) {

					duInfo.wcdma3G.cellList.get(count).name=oriCell;
					count++;
				}
			}

			FileUtil.writeToFile(sb, fileName);

		}catch (Exception e) {
			Logger.logger.error("generate generateBscRelations Scripts exception!", e);
			Logger.getGmoLogger().printError("Error while generating BSC Relations!" + e.getMessage());
		}
	}
	
	
	public void WcdmaLteRelations(SiteCellObj duInfo) {
		HashMap<String,List<String>> map= new HashMap<>();
		for(String UCellString : duInfo.wcdma3G.cells) {
			List<String> list=map.get(UCellString);
			if(list==null) {
				list=new ArrayList<>();
			}
			for(String earfcndl : duInfo.wcdmaLteRelation.earfcnDlList ) {
				list.add(earfcndl);
			}
			map.put(UCellString, list);
		}
		duInfo.wcdmaLteRelation.cellReselectionPriority="7";
		duInfo.wcdmaLteRelation.qRxLevMin="-124";
		duInfo.wcdmaLteRelation.threshHigh="6";
		duInfo.wcdmaLteRelation.threshLow="6";
		duInfo.wcdmaLteRelation.redirectionOrder="1";
		duInfo.wcdmaLteRelation.eutraDetection="True";
	}
	

	/**
	 * Generate SRS files for all LTE cells, for all nodes in sitelist RND having new or existing Lte FDD carriers, where one node is a NSB
	 */
	// [08142020]
	protected void generateSRS()
	{
		try {
			Boolean isNsbIncluded = false;
			Boolean isLteIncluded = false;
			for (String site : sites) {
				SiteCellObj duInfo = tmoCCR.getDUToDUInfo().get(site);

//				if (duInfo.tmoDUInfo.isMixedModeBasebandScope && duInfo.tmoDUInfo.isMMBBNode && duInfo.isNewSite) {
				if (duInfo.isNewSite) {
					isNsbIncluded = true;
				}
				isLteIncluded = tmoCCR.checkNodeCellTechnology(isLteIncluded, duInfo);
			}
			if (isNsbIncluded && isLteIncluded) {
				SectorAddUtil sectorAddUtil = new SectorAddUtil(gmoExecuter, gmoExecuter.getGmoExecUtil(), Logger.getGmoLogger());
				sectorAddUtil.generateLTESRSOutput(ciqs.get("RND").getPath(), siteList);
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateSRS exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating SRS NSB, new carrier file!");
		}
	}
	
	
	private void generateESIExcelSheet() throws IOException {

		Logger.getGmoLogger().printTextWithTimeStamp("Generating ESI_CSV Worksheet");

		for (Entry<String, SiteCellObj> siteEntry : tmoCCR.getDUToDUInfo().entrySet()) {
			SiteCellObj duInfo = siteEntry.getValue();
			String site = siteEntry.getKey();
			
			String fileNodeName = tmoFileRenamingForESI.calculcateFileFolderNodeName(duInfo);	// [11112020] MMBB Var 1 should use existing NR node name
			if (!site.contentEquals(fileNodeName)) {	// [11112020]
				site = fileNodeName;
			}
			
			//+ File.separator + site + "_ESI.csv";
			// String Package = false;
			ArrayList<String> esiCSVarray = new ArrayList<String>();
			
			if (duInfo.tmoDUInfo.isTDDNode //)/ {	 [10082020] For N41 NSB, do not create CSV for TDD node
				&& ((!duInfo.isNewSite && !duInfo.tmoDUInfo.isMixedModeBasebandScope && !duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.tmoDUInfo.isMidBandTdd2CAdd   	// [10222020] Now TDD flag is set during data collection
			    && !duInfo.tmoDUInfo.triggerAir6449SwapScripts							// [08102021] GMO_TMO-131
			    && !duInfo.tmoDUInfo.isTddCarrierAddScope//)							// [12172021] GMO_TMO-206
				&& !duInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope)	// [02152022] GMO_TMO-237
				|| !sites.contains(duInfo.duName)))	 { // [11132020] B41 TDD node, not in sitelist for N41 scope, should be generated separately, not included in output for N41
				continue;
			}
			if (!tmoCCR.rndLteSitesFromSiteName.contains(duInfo.duName) && !duInfo.isNewSite && !duInfo.is5G && !duInfo.tmoDUInfo.isMMBBNode) {		// [12102020] Do not copy scripts for Lte sites not in RND
				continue;
			}

//			String	headers = "Site Name,cu,upgradePackage,market,enm,bbType,duTObbu,dulTOdus,bbNSB,duNSB,bbLSC,duLSC,ecmCapable";
			// [11122020] Add common columns used by other CUs.
			
			//[egovpav]
			//2-9-2022
			//align all ESI.CSV headers to variables in EsiCsvHeader (GMO_TMO-197)
			//String headers = "Site Name,nodename,cu,Technology,upgradePackage,market,enm,bbType,duTObbu,dulTOdus,bbNSB,duNSB,bbLSC,duLSC,bbtobb,ecmCapable,timezone";			
			esiCSVarray.add(TMO_CommonUtil.getEsiCsvHeaders());
			String upGradePackageName = "".equalsIgnoreCase(duInfo.pciSiteObj.release) ? tmoDC.collectUpgradePackageReleaseFromKget(site) : duInfo.pciSiteObj.release;
			// [10092020] Change to full upgrade package name, same as in kget
			if (duInfo.pciSiteObj.upgradePackageId.isEmpty()) {		// Should already be populated for existing or NSB
				String duNameForKgetLookup = TMO_CommonUtil.getDuNameForKgetLookup(duInfo);
				TMODataCollector.collectUpgradePackageIdFromKget(duInfo, duNameForKgetLookup);
			}

			upGradePackageName  = duInfo.pciSiteObj.upgradePackageId;	// Need to use full upgrade package name, not release
			upGradePackageName = upGradePackageName.replaceAll("[\\W]+", "_");		// Replace any non-alphanumeric char, such as "\", " ", "-" with under_score for ESI_CSV
			if (upGradePackageName.isEmpty()) {
				Logger.getGmoLogger().printError("Upgrade package is missing in ESI CSV for " + site);
			}

//			String nodeType =duInfo.nodeType.isEmpty() ? "BB6630" : duInfo.nodeType;
			// [10132020] Calculate node type using both kget and RND inputs
			String nodeType = tmoDC.calculateNodeType(duInfo);
			String bbNsb = "False";
			String duNsb = "False";
			String bbLsc = "False";
			String duLsc = "False";
			// [10212020]
			if (duInfo.isBBU || nodeType.matches("BB.*") || nodeType.isEmpty()) {	// [10092020] Added check for nodeType for nodes, not in sitelist or kget, but included in duInfo for NSB creation
				bbNsb = duInfo.isNewSite ? "True" : "False";
				bbLsc = duInfo.isNewSite ? "False" : "True";
			} else {
				duNsb = duInfo.isNewSite ? "True" : "False";
				duLsc = duInfo.isNewSite ? "False" : "True";
			}

			String ecmCapable = duInfo.isecmcapable ? "True" : "False";		// [10202020] To aid in debugging

//			String market = !"".equalsIgnoreCase(duInfo.getSiteObj().getMarket())? duInfo.getSiteObj().getMarket() : duInfo.subNetwork;
			// [11122020] Add common columns used by other CUs.
			String technology = duInfo.is5G ? "5G" : "4G";
			technology = duInfo.tmoDUInfo.isMMBBNode || duInfo.has2GAnd3GSites ? "MMBB" : technology;
			technology = duInfo.tmoDUInfo.isMidbandMixedModeBasebandScope && duInfo.tmoDUInfo.isLTENode ? "4G" : technology;
			technology = duInfo.tmoDUInfo.isMidbandMixedModeBasebandScope && duInfo.tmoDUInfo.isMMBBNode && !duInfo.tmoDUInfo.isLTENode ? "5G" : technology;
			
			String timezone = duInfo.pciSiteObj.timeZoneARNE.isEmpty() ? duInfo.pciSiteObj.timeZoneSiteBasic : duInfo.pciSiteObj.timeZoneARNE;
			String region = TMODataCollector.calculateMarketRegion(duInfo, timezone);
			if(duInfo.has2GAnd3GSites) {
				esiCSVarray.add(duInfo.gsm2G.cellList.get(0).nodeName + "," + duInfo.gsm2G.cellList.get(0).nodeName + "," + "TMO" + "," + technology + "," + upGradePackageName + "," + region + "," + duInfo.pciSiteObj.enmName + "," + "BB6630"
						+ "," + "False" + "," + "False" + "," + bbNsb + "," + duNsb + "," + bbLsc + "," + duLsc + "," + "False" + "," + ecmCapable + "," + timezone);
			}
			else {
				esiCSVarray.add(site + "," + site + "," + "TMO" + "," + technology + "," + upGradePackageName + "," + region + "," + duInfo.pciSiteObj.enmName + "," + nodeType
						+ "," + "False" + "," + "False" + "," + bbNsb + "," + duNsb + "," + bbLsc + "," + duLsc + "," + "False" + "," + ecmCapable + "," + timezone);
			}

			boolean csvGenerated = false;
			if (esiCSVarray.size() > 1) {
				String esiDir = "";
				esiDir = FileUtil.createDirReturnStr(outputDir + File.separator + "Integration" + File.separator + "ESI_CSV");	
				if(duInfo.has2Gsites || duInfo.has3Gsites || duInfo.has2GAnd3GSites) {
					FileUtil.writeDataToCsvFile(esiCSVarray,esiDir + File.separator + duInfo.gsm2G.cellList.get(0).nodeName + "_ESI.csv");
				}
				else {
					FileUtil.writeDataToCsvFile(esiCSVarray,esiDir + File.separator + site + "_ESI.csv");
				}
				csvGenerated = true;
			}
			if (csvGenerated) {
				Logger.getGmoLogger().printTextWithTimeStamp("CSV file(s) generated.");
				Logger.logger.debug("CSV file(s) generated.");
			}
			else {
				Logger.getGmoLogger().printTextWithTimeStamp("Conditions to trigger CSV not met. CSV file not generated.");
				Logger.logger.debug("Conditions to trigger CSV not met. CSV file not generated.");
			}
				
//			rndSitelistFromSiteNames = tmoCCR.gmoExecUtil.mergeArrays(rndSitelistFromSiteNames, TMODataCollector.getDistinctLteSiteNamesForLteSiteFromRnd(tmoCCR.getDuNameForKgetLookup(duInfo)), true);
		}
	}

	
	/**
	 * This function checks if a SOW will send a zipped script package to the ECI factory to automatically build a new CV for the site 
	 * @param siteList
	 * @param mduTMO
	 * @return
	 */
	protected Boolean checkEciApplicableScope(String siteList)
	{
		Boolean isEciScope = false;
		try {
			Set<String> sites = CommonUtil.getSiteListMatrixSet(siteList);
			if(hasExcalibur4G5G) {
				Set<String> tempsites = new TreeSet<>();
			for(String site: sites) {
				tempsites.addAll(getColumnValues(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), site, "eNodeB Name"));
			}
				sites=tempsites;
			}
			for (String site : sites) {
				SiteCellObj duInfo = tmoCCR.getDUToDUInfo().get(site);
				if (duInfo.tmoDUInfo.getIsMixedModeBasebandScope()) {
					isEciScope = true;
					return isEciScope;
				}
				if (duInfo.isNewSite) {
					isEciScope = true;
					return isEciScope;
				}

				if (duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) {	// [10192020] Just in case this method gets re-used
					isEciScope = true;
					return isEciScope;
				}
				
				// [08172021] GMO_TMO-131 Always zip ESI_Input folder, even if not ECI scope, else ISF will not accept it, while closing WO
				isEciScope = true;
				return isEciScope;
			}
		}
		catch (Exception e) {
			Logger.logger.error("checkEciApplicableScope exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error checking for ECI applicable scope!");
		}

		return isEciScope;
	}
	
	/**
	 * This function copies and renames files into the Integration directory for use by EESI/REESI
	 * @throws Exception
	 * @throws FileNotFoundException
	 * @throws IOException
	 */
	protected void generateEesiFiles() throws Exception, FileNotFoundException, IOException
	{
		String integrationDirForEESI ="";
		String siteDirForEESI = "";
		String siteBBLSCSOWDirForEESI = "";
		String siteDirForEESIRollback = "";		// [06302020]
		String siteDirForEESILTECleanUp = "";   // [07302020]
		String siteAutoBot = "";
		try {
			TMOMixedModeBasebandScripts tmoMixedModeBasebandScripts = new TMOMixedModeBasebandScripts(this);
			
			for (String site : sites) {
				String siteDir="";
				String siteDirBackup="";		// In case need to delete empty directory
				
				SiteCellObj duInfo = tmoCCR.getDUToDUInfo().get(site);
				if(!duInfo.has2GAnd3GSites) {
					siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + String.join("_", sites));
					siteDirBackup = siteDir;
				}
				String upGradePackageName =  "".equalsIgnoreCase(duInfo.pciSiteObj.release) ? tmoDC.collectUpgradePackageReleaseFromKget(site) : duInfo.pciSiteObj.release;
//				String upGradePackageName = duInfo.pciSiteObj.upgradePackageId.indexOf("_")>-1?
//						duInfo.pciSiteObj.upgradePackageId.substring(duInfo.pciSiteObj.upgradePackageId.indexOf("_")+1) : "";
				System.out.println("Current Site Processing : " + site);
				if("".equalsIgnoreCase(upGradePackageName)) {
					Logger.logger.error("upgrade package is missing!");
					Logger.getGmoLogger().printError("upgrade package is missing! Files will not be moved, renamed for E-ESI/ECI automation");
					return;
				}
				if (duInfo.tmoDUInfo.isMixedModeBasebandScope || duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope ||
					duInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope || duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope) {
					String fileNodeName = tmoFileRenamingForESI.calculcateFileFolderNodeName(duInfo);		// [06172020]

					String esiScope = !duInfo.isNewSite ? "BBLSC" : "BBNSB";		// [10202020]
					
					integrationDirForEESI = FileUtil.createDirReturnStr(outputDir + File.separator + "Integration");
				
					siteDirForEESI = FileUtil.createDirReturnStr(integrationDirForEESI + File.separator + "ESI_Input" + File.separator + fileNodeName + File.separator + fileNodeName);
					siteBBLSCSOWDirForEESI = FileUtil.deleteAndCreateDir(siteDirForEESI + File.separator + "Mobile_" + esiScope + "_" + upGradePackageName);		// [10202020]
					
//					siteBBLSCSOWDirForEESI = FileUtil.deleteAndCreateDir(siteDirForEESI + File.separator + "Mobile_BBLSC_" + upGradePackageName);

					//MMBB
					if (!"".equalsIgnoreCase(siteDir) && !"".equalsIgnoreCase(siteBBLSCSOWDirForEESI)) {
//						String scopeName = duInfo.tmoDUInfo.isMMBBNode ? "5GBBLSC" : "BBLSC";
						String scopeName = duInfo.tmoDUInfo.isMMBBNode ? "5G" + esiScope : esiScope;		// [10202020]
						scopeName = scopeName.contains("NSB") && !duInfo.tmoDUInfo.isMMBBNode && !duInfo.is5G ? "LTE" + scopeName : scopeName;	// [01192021] 4G (Anchor) new site in sitelist with existing MMBB in inputs
						tmoFileRenamingForESI.copyRenameFilesIntoDirectory(duInfo, scopeName, new File(siteDir), new File(siteBBLSCSOWDirForEESI));
						tmoFileRenamingForESI.renameFileNames(duInfo, scopeName, new File(siteBBLSCSOWDirForEESI));
					}
					if (duInfo.tmoDUInfo.isMMBBNode) {	// [0632020] Create Rollback directory, scripts for MMBB
						siteDirForEESIRollback = FileUtil.createDirReturnStr(siteDirForEESI + "_Rollback");
						FileUtil.moveFilesToFolder(siteBBLSCSOWDirForEESI, siteDirForEESIRollback, ".+(EXTERNALEUTRANCELLFDDDELETE|ExternalEUtranCellFDD_delete)+.+", true);		// Currently only labeled as E61 script
					}
					if(!duInfo.tmoDUInfo.isMMBBNode && tmoMixedModeBasebandScripts.checkIfMovingCellExists(duInfo)) {
						siteDirForEESILTECleanUp = FileUtil.createDirReturnStr(siteDirForEESI + "_CleanUp");
						FileUtil.moveFilesToFolder(siteBBLSCSOWDirForEESI, siteDirForEESILTECleanUp, ".+(EXTERNALEUTRANCELLFDDDELETE|ExternalEUtranCellFDD_delete)+.+", true);		// Currently only labeled as E61 script
					}

					List<String> ignoreLines = new ArrayList<>();
					ignoreLines.add("confb+");
					ignoreLines.add("confb-");
					ignoreLines.add("gs+");
					ignoreLines.add("gs-");
					ignoreLines.add("lt all");
					ignoreLines.add("u+");
					ignoreLines.add("u-");
					ignoreLines.add("alt");


					List<File> autobotFileList = Arrays.asList(new File(siteBBLSCSOWDirForEESI).listFiles());
					TreeMap<Integer,File> sortedFileList = getFileSequence(autobotFileList, duInfo);
					if(!duInfo.tmoDUInfo.isMMBBNode && !"".equalsIgnoreCase(siteBBLSCSOWDirForEESI)) {
						siteAutoBot = FileUtil.deleteAndCreateDir(integrationDirForEESI + File.separator + "ESI_Input" + File.separator + fileNodeName + File.separator + fileNodeName + "_Autobot");

						// [06102020]
						List<String> ignoreFilesList = new ArrayList<>();	// [06102020] List of substring in file names to be NOT included in combined script
						List<File> moveFilesList = new ArrayList<File>();	// [06102020] List of files to not include in combined script, but be moved to the Autobot directory

						ignoreFilesList.add("(E50|E95)");					// for example: Lxx#####x_E50_GURTANCELLRELATION_02_Node_GutranCellRelation.mos. [10202020] E50 renumbered to E95
						ignoreFilesList.add("Mobatch_sitelist.txt");		// [06252020] for running Mobatch on generic script in folder (required for 4sec MMBB)
						for (String ignoreFileStr : ignoreFilesList) {
							for (File autobotFile : autobotFileList) {	
								if (autobotFile.getName().matches(fileNodeName + "_" + ignoreFileStr + "_.*" ) ||
									(autobotFile.getName().matches("(" + fileNodeName + "_+)*" + ignoreFileStr))) {	// [06292020] For Mobatch_sitelist
									moveFilesList.add(autobotFile);
								}
							}
						}
						for (File moveFile : moveFilesList) {
							if (sortedFileList.containsValue(moveFile)) {
								for (Entry<Integer, File> file : sortedFileList.entrySet()) {
									if (file.getValue().equals(moveFile)) {
										sortedFileList.remove(file.getKey());		// Do not include file in combined script file
										break;
									}
								}
							}
							FileUtil.copyFileNew(moveFile, new File(siteAutoBot + File.separator + moveFile.getName()));	// Copy file to another directory
						}

						PrintWriter pw = new PrintWriter(siteAutoBot + File.separator + fileNodeName + "_Combined.mos");
						pw.println("############ LTE Node combined script ########################");
						pw.println("lt all");
						pw.println("gs+");
						pw.println("confb+");
						pw.println("u+");
						pw.println("###################Node check#################");
						// TC_361
						String nodeType = (duInfo.isBBU || duInfo.nodeType.matches("BB.*") || duInfo.outputFormat.contentEquals("G2")) ? "BB" : duInfo.nodeType;
						pw.println(tmoCCR.generateGenericNodeNameBlock(duInfo.duName, nodeType).toString());	// [10272020]		
//						pw.println(tmoCCR.generateGenericFingerPrintBlock(duInfo.duName).toString());			

						for(Map.Entry<Integer,File> lteFile : sortedFileList.entrySet()) {
							BufferedReader br = null;
							String line = "";
							if(lteFile.getValue().isFile())
								br = new BufferedReader(new FileReader(lteFile.getValue())); 
							if(br != null) {
								while((line = br.readLine()) != null){
									if(line.startsWith("get Lm=1 ^fingerprint$") || line.matches("get \\. \\p{Alpha}+ > \\$Nodename.*")) {	// [10282020] Updated to add check for 'get . logicalName > $Nodename' or 'get . ManagedElementId > $Nodename'
										while (true) {
											line = br.readLine();	
											if (line != null
													&& (line.trim().startsWith("fi") )) {
												line = br.readLine();
												break;
											}
										}
									}
									if(line != null) {
										if((ignoreLines.contains(line.trim()))
												||(line.trim().startsWith("cvm") && !line.trim().startsWith("cvms $Nodename_PreMMBB_$date") &&!line.trim().startsWith("cvms $Nodename_PostMMBB_$date")))	// [06092020] remove cvms or cvmk
											continue;
									
										pw.println(line);
										
										if(line.trim().startsWith("$date = `date +%y%m%d-%H%M") && !ignoreLines.contains(line.trim()))		// [06092020] deleted ending ' char
											ignoreLines.add(line.trim());
									}
								}
							}

							if(br!=null) {
								br.close();
							}
						}
						if(pw!=null) {
							pw.println("u-");
							pw.println("gs-");
							pw.println("confb-");
							pw.println("lt all");
							pw.println("alt");
							pw.close();
						}
					}
				}
				
				if (duInfo.tmoDUInfo.isMidbandMixedModeBasebandScope) {
					String fileNodeName = tmoFileRenamingForESI.calculcateFileFolderNodeName(duInfo);		// [06172020]
					String esiScope = !duInfo.isNewSite ? "BBLSC" : "LTEBBNSB";		// [10202020]
					integrationDirForEESI = FileUtil.createDirReturnStr(outputDir + File.separator + "Integration");
					siteDirForEESI = FileUtil.createDirReturnStr(integrationDirForEESI + File.separator + "ESI_Input" + File.separator + fileNodeName + File.separator + fileNodeName);
					siteBBLSCSOWDirForEESI = FileUtil.deleteAndCreateDir(siteDirForEESI + File.separator + "Mobile_" + esiScope + "_" + upGradePackageName);		// [10202020]
				}

				integrationDirForEESI = FileUtil.createDirReturnStr(outputDir + File.separator + "Integration");
				if(duInfo.has2GAnd3GSites) {
					siteDirForEESI = FileUtil.createDirReturnStr(integrationDirForEESI + File.separator + "ESI_Input" + File.separator + duInfo.gsm2G.cellList.get(0).nodeName + File.separator + duInfo.gsm2G.cellList.get(0).nodeName );
				}
				else if(!duInfo.tmoDUInfo.isMidbandMixedModeBasebandScope){
					siteDirForEESI = FileUtil.createDirReturnStr(integrationDirForEESI + File.separator + "ESI_Input" + File.separator + site + File.separator + site);
				}
				
				if(duInfo.tmoDUInfo.isLowBandSetUp1DReconfig) {
					duInfo.isNewSite = true;
				}
				
				if (duInfo.isNewSite) {	// [08182020] Moved to separate if statement
					
					//To avoid duplicate scripts in ESI_Input.zip for LTE site for MMBB scopes.
					boolean ignoreScope = tmoDC.ignoreFileRenamingForScope(duInfo);
					if(ignoreScope) {
						continue;
					}
					
					String siteBBNSBSOWDirForEESI = siteDirForEESI + File.separator + "Mobile_BBNSB_" + upGradePackageName;
					if((duInfo.tmoDUInfo.isMixedModeBasebandScope && !(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) || duInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope) {				
						siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + "01_" + site + "_BBNSB");
					}
					else if(duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope) {
						if(duInfo.tmoDUInfo.isLowBandMMBBVariation) {
							siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + "01_" + site + "_BBNSB");
						}
						else if(duInfo.tmoDUInfo.isMidBandTddMMBBVariation) {
							siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + "02_" + site + "_BBNSB");
						}
					}
					else /*if (!duInfo.is5G)*/ {	// [08202020] 4G NSB scripts parent directory are different if midband or not. Need to start at root output directory
						siteDir = FileUtil.createDirReturnStr(outputDir);
						FileUtil.deleteAndCreateDir(siteBBNSBSOWDirForEESI);	// [10202020] Folder already deleted/created for MMBB scope but not other NSB
					}
					/*else {													// [10202020] Removed so 5G will look in all output subfolders for node scripts
							siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + site);
					}*/
					String scopeName="";
					if(duInfo.is5G && !duInfo.tmoDUInfo.isMidBandFddMMBBVariation) {
						 scopeName="5GBBNSB";
					}
					else if((duInfo.has2GAnd3GSites)) {
						 scopeName="2G3GBBNSB";
					}
					else {
						 scopeName="LTEBBNSB";
					}

					tmoFileRenamingForESI.copyRenameFilesIntoDirectory(duInfo, scopeName, new File(siteDir), new File(siteBBNSBSOWDirForEESI));
					tmoFileRenamingForESI.renameFileNames(duInfo, scopeName, new File(siteBBNSBSOWDirForEESI));
				}
				// [10202020] NSB will no longer have BBLSC folder
				else if (!duInfo.tmoDUInfo.isMixedModeBasebandScope) {	// [08182020]
					siteBBLSCSOWDirForEESI = FileUtil.deleteAndCreateDir(siteDirForEESI + File.separator + "Mobile_BBLSC_" + upGradePackageName);
					String scopeName = duInfo.is5G ? "5GBBLSC" : "BBLSC";
					if(duInfo.isNRNodeLive && (duInfo.tmoDUInfo.isMidBandTdd2CAddMixedModeBaseBandScope || duInfo.tmoDUInfo.isLiveLowBandAndTdd2CAddMixedModeBaseBandScope || duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope)) {
						scopeName = (duInfo.tmoDUInfo.isMMBBNode) ? "5GBBLSC":scopeName;
					}
					scopeName = duInfo.tmoDUInfo.isMidbandMixedModeBasebandScope && duInfo.tmoDUInfo.isLTENode ? "BBLSC":scopeName;
					siteDir = FileUtil.createDirReturnStr(outputDir);

					tmoFileRenamingForESI.copyRenameFilesIntoDirectory(duInfo, scopeName, new File(siteDir), new File(siteBBLSCSOWDirForEESI));
					tmoFileRenamingForESI.renameFileNames(duInfo, scopeName, new File(siteBBLSCSOWDirForEESI));
				}

				else if ((duInfo.tmoDUInfo.isMixedModeBasebandScope || duInfo.tmoDUInfo.isTDDMixedModeBaseBandScope || duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope || duInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope) && duInfo.tmoDUInfo.isMMBBNode && !duInfo.isNRNodeLive) {
					String scopeName = duInfo.is5G ? "5GBBLSC" : "BBLSC";

					tmoFileRenamingForESI.copyRenameFilesIntoDirectory(duInfo, scopeName, new File(siteDir), new File(siteBBLSCSOWDirForEESI));
					tmoFileRenamingForESI.renameFileNames(duInfo, scopeName, new File(siteBBLSCSOWDirForEESI));
				}
				
				// [08172021] GMO_TMO-131, delete just created folder, if empty
				FileUtil.deleteDirIfEmpty(siteDirBackup);
			}

			String region = "";		// [11122020]	
			String enm = "";		// [11122020]	
			String timeZone = "";	// [11122020]	
			String subNetwork = "";	// [01052020]	
			ArrayList <String> rndSitelistFromSiteNames = new ArrayList<String>();					// [09142020] 
			// [01052021]
			
			rndSitelistFromSiteNames = tmoCCR.rndLteSitesFromSiteName;

			for (Entry<String, SiteCellObj> siteEntry : tmoCCR.getDUToDUInfo().entrySet()) {		// [08182020]
				SiteCellObj duInfo = siteEntry.getValue();

				String site = tmoFileRenamingForESI.calculcateFileFolderNodeName(duInfo);
				if (!sites.contains(duInfo.duName) &&			// Move, rename scripts for any node, for which data was retrieved, but not included in sitelist nodes
					rndSitelistFromSiteNames.contains(duInfo.duName)) {	// [12102020] Do not copy scripts for (Lte) sites not in RND
					String upGradePackageName =  "".equalsIgnoreCase(duInfo.pciSiteObj.release) ? tmoDC.collectUpgradePackageReleaseFromKget(site) : duInfo.pciSiteObj.release;
					if("".equalsIgnoreCase(upGradePackageName)) {
						String duNameForKgetLookup = TMO_CommonUtil.getDuNameForKgetLookup(duInfo);
						upGradePackageName =  tmoDC.collectUpgradePackageReleaseFromKget(duNameForKgetLookup);

						if("".equalsIgnoreCase(upGradePackageName)) {
							Logger.logger.error("upgrade package is missing!");
							Logger.getGmoLogger().printWarning("upgrade package is missing! Files will not be moved, renamed for E-ESI/ECI automation");
							return;
						}
					}
					
					if (duInfo.getSiteObj().isIs4gAnchor()) {		// [1132020] B41 (not included in N41 sitelist) is generated by Multi-Du option
						continue;
					}

					integrationDirForEESI = FileUtil.createDirReturnStr(outputDir + File.separator + "Integration");
					siteDirForEESI = FileUtil.createDirReturnStr(integrationDirForEESI + File.separator + "ESI_Input" + File.separator + site + File.separator + site);

					siteBBLSCSOWDirForEESI = FileUtil.deleteAndCreateDir(siteDirForEESI + File.separator + "Mobile_BBLSC_" + upGradePackageName);
					String scopeName = duInfo.is5G ? "5GBBLSC" : "BBLSC";
					String siteDir = FileUtil.createDirReturnStr(outputDir);

					tmoFileRenamingForESI.copyRenameFilesIntoDirectory(duInfo,  scopeName, new File(siteDir), new File(siteBBLSCSOWDirForEESI));
					tmoFileRenamingForESI.renameFileNames(duInfo, scopeName, new File(siteBBLSCSOWDirForEESI));
				}
				else if (region.isEmpty() && enm.isEmpty() && timeZone.isEmpty()) {	// [11122020] Save data for nodes not included in sitelist, with no data collected, but have scripts generated
					region = duInfo.pciSiteObj.esi_Region;		// [11122020]	
					enm = duInfo.pciSiteObj.enmName;			// [11122020]	
					timeZone = duInfo.pciSiteObj.timeZoneARNE.isEmpty() ? duInfo.pciSiteObj.timeZoneSiteBasic : duInfo.pciSiteObj.timeZoneARNE;	// [11122020]	
					subNetwork = duInfo.subNetwork;				// [01052020]
				}
			}

			// [09142020] Workaround to rename scripts for sites not stored in objects or sitelist but exist in RND and have a parsed kget
			// [01052021] Added collection of CM CIQ market data for FDD LTE nodes included in RND, not in sitelist, no kget in inputs
			for(int i = 0; i < rndSitelistFromSiteNames.size() ; i++) {
				String rndSite = rndSitelistFromSiteNames.get(i);
				if (!sites.contains(rndSite) && !tmoCCR.getDUToDUInfo().containsKey(rndSite)) {			// Move, rename scripts for any other nodes in RND, not included in sitelist nodes and with no data stored
					String upGradePackageName =  tmoDC.collectUpgradePackageReleaseFromKget(rndSite);
					
					SiteCellObj rndDuInfo = new SiteCellObj();
					rndDuInfo.duName = rndSite;
					rndDuInfo.subNetwork = subNetwork;			// [01052020]
					if (upGradePackageName.isEmpty()) {		// [01052021]
						String duNameForKgetLookup = TMO_CommonUtil.getDuNameForKgetLookup(rndDuInfo);
						String lteFddSiteNameString = TMODataCollector.getDistinctLteSiteNamesMatchesFDDType(duNameForKgetLookup);
						Boolean l19l21Cells = false;						// Only collect data if nodes contains L19 (B) or L21 (L) cells
						ArrayList<String> rowDataArray = TMODataCollector.getDistinctCellFddNamesForLteSiteFromRnd(rndSite);
						for(String eUtranCellFddId : rowDataArray) {
							l19l21Cells = eUtranCellFddId.matches("^(B|L).+") ? true : l19l21Cells;
						}
						
						if(rndSite.matches(lteFddSiteNameString.replaceAll("_", "|")) && l19l21Cells) {	// Collect additional data for FDD lte nodes with no kget
//							rndDuInfo.isNewSite = true;
							rndDuInfo.isBBU = true;
							TMODataCollector.collectSiteDataFromMarketDataFile(rndDuInfo);	// Need additional data to properly fill in ESI_CSV

							upGradePackageName = rndDuInfo.pciSiteObj.release;
						}
					}
					
					if(!upGradePackageName.isEmpty()) {		// Check if site exists in kget
//						SiteCellObj rndDuInfo = new SiteCellObj();
//						rndDuInfo.duName = rndSite;
						rndDuInfo.pciSiteObj.release = upGradePackageName;
						rndDuInfo.pciSiteObj.esi_Region = region;			// [11122020]
						rndDuInfo.pciSiteObj.enmName = enm;					// [11122020]
						rndDuInfo.pciSiteObj.timeZoneARNE = timeZone;		// [11122020]

						tmoCCR.getDUToDUInfo().put(rndSite, rndDuInfo);		// [09152020]	Add to overall map so ESI.CSV file gets generated for this node as well

						integrationDirForEESI = FileUtil.createDirReturnStr(outputDir + File.separator + "Integration");
						siteDirForEESI = FileUtil.createDirReturnStr(integrationDirForEESI + File.separator + "ESI_Input" + File.separator + rndSite + File.separator + rndSite);

						siteBBLSCSOWDirForEESI = FileUtil.deleteAndCreateDir(siteDirForEESI + File.separator + "Mobile_BBLSC_" + upGradePackageName);
						String scopeName = "BBLSC";
						String siteDir = FileUtil.createDirReturnStr(outputDir);

						tmoFileRenamingForESI.copyRenameFilesIntoDirectory(rndDuInfo,  scopeName, new File(siteDir), new File(siteBBLSCSOWDirForEESI));
						tmoFileRenamingForESI.renameFileNames(rndDuInfo, scopeName, new File(siteBBLSCSOWDirForEESI));
					}
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateEesiFiles exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating EESI, renamed script files!");
		}
	}

	private boolean checkExCal(String s) {
		
		return hasExcalibur4G5G && !s.startsWith("L");
	}

	/**
	 * @param outputDir
	 */
	private void zipIntegrationFolder(String outputDir) {

		try {
			File integrationDir = new File(outputDir + File.separator + "Integration");
			if (integrationDir.exists()) {
				FileOutputStream fos = new FileOutputStream(
						integrationDir.getAbsolutePath() + File.separator + "ESI_Input.zip");
				ZipOutputStream zipOut = new ZipOutputStream(fos);
				ArrayList<File> files = new ArrayList<File>(Arrays.asList(integrationDir.listFiles()));
				for(File file : files) {
					if(file.getName().equalsIgnoreCase("ESI_Input.zip") || file.getName().equalsIgnoreCase("ESI_CSV"))
						continue;
					if(file.isDirectory())
						addFolderToZip("", file.getAbsolutePath(), zipOut);
					FileUtil.deleteFolder(file);
					if(file.isFile()) {
						addFileToZip("", file.getAbsolutePath(), zipOut);
						FileUtil.deleteFile(file.getAbsolutePath());
					}

				}
				zipOut.close();
				fos.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("zipIntegrationFolder exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error Integration Folder files!");
		}
	}

	private void addFileToZip(String path, String srcFile, ZipOutputStream zip)
			throws Exception {

		try {
			File folder = new File(srcFile);
			if (folder.isDirectory()) {
				addFolderToZip(path, srcFile, zip);
			} else {
				byte[] buf = new byte[1024];
				int len;
				FileInputStream in = new FileInputStream(srcFile);
				zip.putNextEntry(new ZipEntry(path + "/" + folder.getName()));
				while ((len = in.read(buf)) > 0) {
					zip.write(buf, 0, len);
				}
				in.close();
			}
		}
		catch (Exception e) {
			Logger.logger.error("addFileToZip exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error adding Files to Zipped Folder!");
		}
	}

	private void addFolderToZip(String path, String srcFolder, ZipOutputStream zip)
			throws Exception {
		File folder = new File(srcFolder);

		for (String fileName : folder.list()) {
			if (path.equals("")) {
				addFileToZip(folder.getName(), srcFolder + "/" + fileName, zip);
			} else {
				addFileToZip(path + "/" + folder.getName(), srcFolder + "/" + fileName, zip);
			}
		}
	}
		   
		   
	private TreeMap<Integer,File> getFileSequence(List<File> autobotFileList, SiteCellObj duInfo){
		TreeMap<Integer,File> fileSequence = new TreeMap<>();
		Integer maxFileSequence = 200;	// [06152020] Break the loop if files not found according to search. Current highest file number for E-ESI is 71
		try {
			if(autobotFileList==null || autobotFileList.size()==0) {
				return fileSequence;
			}
			List<File> autobotFileListLoc = new ArrayList<>();
			for(File autobotFile : autobotFileList) {
				if(autobotFile.getName().startsWith(duInfo.duName + "_E")) {
					autobotFileListLoc.add(autobotFile);
				}
			}
			int i=0;
			while(fileSequence.size()!=autobotFileListLoc.size() && i < maxFileSequence) {
				String sequenceNumber = i<=9 ? "0" + i:"" + i;
				for(File autobotFile : autobotFileListLoc) {
					if(autobotFile.getName().startsWith(duInfo.duName + "_E" + sequenceNumber) && autobotFile.getName().endsWith(".mos")) {
						fileSequence.put(i, autobotFile);
					}
				}
				i++;
			}
		}
		catch (Exception e) {
			Logger.logger.error("getFileSequence exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error getting file sequence for autobot file list!");
		}

		return fileSequence;
	}

	
	/**
	 * Function to retrieve LKFs for TMO nodes
	 */
	public void retrieveTmoLKFs() {
		try {
			LkffetchUtil lkfFetchUtil = new LkffetchUtil();
			lkfFetchUtil.setVerbose(false);

			String integrationDirForEESI = FileUtil.createDirReturnStr(outputDir + File.separator + "Integration");

			for (Entry<String, SiteCellObj> siteEntry : tmoCCR.getDUToDUInfo().entrySet()) {
				SiteCellObj duInfo = siteEntry.getValue();
				String fileNodeName = tmoFileRenamingForESI.calculcateFileFolderNodeName(duInfo);		// [06172020]
				String site = fileNodeName;
				String nodeType = duInfo.nodeType.isEmpty() ? "BB6630" : duInfo.nodeType;
				if(!duInfo.has2GAnd3GSites) {
					// [10132020] Calculate node type using both kget and RND inputs
					nodeType = tmoDC.calculateNodeType(duInfo);
				}
				String siteDirForEESI="";
				String parSiteDirForEESI="";
				if(duInfo.has2Gsites|| duInfo.has3Gsites || duInfo.has2GAnd3GSites) {
					siteDirForEESI = FileUtil.createDirReturnStr(integrationDirForEESI + File.separator + "ESI_Input" + File.separator + duInfo.gsm2G.cellList.get(0).nodeName);
				}
				else {
					parSiteDirForEESI = FileUtil.createDirReturnStr(integrationDirForEESI + File.separator + "ESI_Input" + File.separator + site);
					siteDirForEESI = FileUtil.createDirReturnStr(parSiteDirForEESI + File.separator + site);
				}
				String siteSOWDirForEESI = "";
				File siteDir = new File(siteDirForEESI);
				ArrayList<File> files = new ArrayList<File>();
				if (siteDir.exists()) {
					FileUtil.addfiles(new File(siteDirForEESI), files);
					for(File file : files) {
						if(siteSOWDirForEESI.isEmpty()) {
							if (file.getAbsolutePath().contains("BB")) {	// "DU2BB", "BBLSC", BBNSB"... Check directory has multiple files which implies it needs more than just relation updates
								if (file.getName().contains("SITEBASIC") || file.getName().contains("ADD")) {		// This covers DU2BB, BBLSC and BBNSB per current TMO_CONFIG.xlsx
									siteSOWDirForEESI = file.getParent();
									break;
								}
							}
						}
					}
				}

				if (!siteSOWDirForEESI.isEmpty()) {
					if (duInfo.tmoDUInfo.isMixedModeBasebandScope && !duInfo.isNewSite) {
						if (duInfo.tmoDUInfo.isMMBBNode && !duInfo.getNrSiteObj().getgNBDUNameOld().isEmpty()) {
							site = duInfo.getNrSiteObj().getgNBDUNameOld();
						} else {
							site = "";
						}
					}
					else if (duInfo.isNewSite) {
					}
					else {
						site = "";
					} 
				}
				
				if (!site.isEmpty() && !siteSOWDirForEESI.isEmpty()) {
					String fingerPrint = "";
					if(duInfo.has2GAnd3GSites) {
						 fingerPrint = duInfo.pciSiteObj.fingerPrint.isEmpty() ? duInfo.gsm2G.cellList.get(0).nodeName : duInfo.pciSiteObj.fingerPrint;	// [10292020] N41 fingerprint is node name + "A"
					}
					else {
						 fingerPrint = duInfo.pciSiteObj.fingerPrint.isEmpty() ? site : duInfo.pciSiteObj.fingerPrint;	// [10292020] N41 fingerprint is node name + "A"
					}
					String lkfFilename = "";
					if(hasExcaliburSmallCells) {
						lkfFilename = lkfFetchUtil.downloadLatestLKFForCU(site, nodeType, siteSOWDirForEESI);
					}else {
						lkfFilename = lkfFetchUtil.downloadLatestLKFForCU(fingerPrint, nodeType, siteSOWDirForEESI);
					}
					if (lkfFilename != null && !lkfFilename.isEmpty()) {
						Logger.getGmoLogger().printTextWithTimeStamp("LKF downloaded for " + site + ".");
						duInfo.pciSiteObj.setLkfFilename(lkfFilename);
					} else {
						if(hasExcaliburSmallCells) {
						Logger.getGmoLogger().printErrorStandard(ErrorCategory.LKF_ISSUE, ErrorSubcategory.LKF_ISSUE,"LKF NOT downloaded for " + site + (fingerPrint.contentEquals(site) ? "." : ", using fingerprint " + site + "."));	// [10292020]
						}else {
							Logger.getGmoLogger().printErrorStandard(ErrorCategory.LKF_ISSUE, ErrorSubcategory.LKF_ISSUE,"LKF NOT downloaded for " + site + (fingerPrint.contentEquals(site) ? "." : ", using fingerprint " + fingerPrint + "."));	// [10292020]
						}
						// [10222020] Ada requested to give error if LKF not found
					}
				}
				else if (siteSOWDirForEESI.isEmpty() && siteDir.exists() && files.isEmpty()) {	// [08102021] GMO_TMO-131, delete empty folder (was just created)
					siteDir.delete();
					if (!parSiteDirForEESI.isEmpty()) {
						File parSiteDir = new File(parSiteDirForEESI);
						if (parSiteDir.exists()) {
							files = new ArrayList<File>();
							FileUtil.addfiles(parSiteDir, files);
							if (files.isEmpty()) {
								parSiteDir.delete();
							}
						}
					}
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("retrieveTmoLKFs exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error retrieving LKFs!");
		}
	}

	
	/**
	 * Function to retrieveOSSNodeProtocol for TMO nodes
	 */
	private void retrieveOSSNodeProtocol() {
		try {
			String integrationDirForEESI ="";
			String siteDirForEESI = "";
			String siteBBLSCSOWDirForEESI = "";
			String siteDirForEESIRollback = "";		// [06302020]
			String siteAutoBot = "";

			for (Entry<String, SiteCellObj> siteEntry : tmoCCR.getDUToDUInfo().entrySet()) {
				SiteCellObj duInfo = siteEntry.getValue();
				String site = siteEntry.getKey();
				if(!duInfo.isNewSite|| duInfo.has2GAnd3GSites) continue;
				String upGradePackageName = duInfo.pciSiteObj.release;	// [06022020] This is now stored for MMBB from kget, not CMCIQ. Calculated from upgradePackageId 
//				String upGradePackageName = duInfo.pciSiteObj.upgradePackageId.indexOf("_")>-1?	duInfo.pciSiteObj.upgradePackageId.substring(duInfo.pciSiteObj.upgradePackageId.indexOf("_")+1) : "";
				if("".equalsIgnoreCase(upGradePackageName)) {
					Logger.logger.error("upgrade package is missing exception!");
					Logger.getGmoLogger().printError("upgrade package is missing exception!");
					return;
				}
				integrationDirForEESI = FileUtil.createDirReturnStr(outputDir + File.separator + "Integration");
				siteDirForEESI = FileUtil.createDirReturnStr(integrationDirForEESI + File.separator + "ESI_Input" + File.separator + site + File.separator + site);
				siteBBLSCSOWDirForEESI = FileUtil.createDirReturnStr(siteDirForEESI + File.separator + "Mobile_BBNSB_" + upGradePackageName);
				try {
					List<String> templatePaths = FileUtil.getLinesFromTemplateNamesThatMatches(".*templates/lte/sector_add/tmobile/multidusectoradd/osf/.*" + duInfo.pciSiteObj.enmName.replaceAll("[-_]","") + ".*");
					if (!templatePaths.isEmpty()) {
						String ossNodeProtocolFile = RemoteTemplate.getXLSFileFromServer(templatePaths.get(0), FileUtil.getCmCiqDirectory() + File.separator + templatePaths.get(0).replaceAll(".*/", ""), false);
						FileUtil.copyFile(new File(ossNodeProtocolFile), new File(siteBBLSCSOWDirForEESI + File.separator + site + "_" + new File(ossNodeProtocolFile).getName()));
						String ossNodeProtocolFilePath = siteBBLSCSOWDirForEESI + File.separator + site + "_" + new File(ossNodeProtocolFile).getName();
						if(duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD || duInfo.has2Gsites||duInfo.has3Gsites) {
							FileUtil.replaceContentInFile(ossNodeProtocolFilePath, "<subjectName>CN=[\\w]+-", "<subjectName>CN=" + site + "-");
						}
						else {
							FileUtil.replaceContentInFile(ossNodeProtocolFilePath, "<subjectName>CN=[\\w]+-", "<subjectName>CN=" + site + "-");
							FileUtil.replaceContentInFile(ossNodeProtocolFilePath, "<networkManagedElementId>[\\w]+<", "<networkManagedElementId>" + site + "<");
							FileUtil.replaceContentInFile(ossNodeProtocolFilePath, "<subjectAltName>DNS:[\\w]+\\.TMobile.US<", "<subjectAltName>DNS:" + site + ".TMobile.US<");
							
						}
						
						duInfo.pciSiteObj.setOssNodeProtocolFile(site + "_" + new File(ossNodeProtocolFile).getName());
					}
					else if (!duInfo.pciSiteObj.enmName.isEmpty()) {
						Logger.getGmoLogger().printWarning("Could not find ossNodeProtocol file path, in templatesNames.txt, for " + duInfo.pciSiteObj.enmName + ". Please advise the GMO team.");
					}
				}
				catch (Exception e) {
					Logger.logger.error("calculateEnmId exception! duName=" + duInfo.duName, e);
					Logger.getGmoLogger().printError("Error calculating Enm ID from ossNodeProtocol file for " + duInfo.duName + "!");
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("retrieveOSSNodeProtocol exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error retrieving OSS Node Protocol!");
		}
	}
	
	
	private void retrieve2gOSSNodeProtocol() {
		try {
			for (Entry<String, SiteCellObj> siteEntry : tmoCCR.getDUToDUInfo().entrySet()) {
				SiteCellObj duInfo = siteEntry.getValue();
				String site = siteEntry.getKey();
				if(!duInfo.isNewSite|| !duInfo.has2GAnd3GSites) continue;
				String upGradePackageName = duInfo.pciSiteObj.release;	// [06022020] This is now stored for MMBB from kget, not CMCIQ. Calculated from upgradePackageId 
//				String upGradePackageName = duInfo.pciSiteObj.upgradePackageId.indexOf("_")>-1 ? duInfo.pciSiteObj.upgradePackageId.substring(duInfo.pciSiteObj.upgradePackageId.indexOf("_")+1) : "";
				if("".equalsIgnoreCase(upGradePackageName)) {
					Logger.logger.error("upgrade package is missing exception!");
					Logger.getGmoLogger().printError("upgrade package is missing exception!");
					return;
				}
				try {
					List<String> templatePaths = FileUtil.getLinesFromTemplateNamesThatMatches(".*templates/lte/sector_add/tmobile/multidusectoradd/osf/.*" + duInfo.pciSiteObj.enmName.replaceAll("[-_]","") + ".*");
					if (!templatePaths.isEmpty()) {
						
						String esi_path = outputDir + File.separator + "Integration" + File.separator + "ESI_Input" + File.separator + duInfo.gsm2G.cellList.get(0).nodeName + File.separator + duInfo.gsm2G.cellList.get(0).nodeName ;
						esi_path=esi_path + File.separator + "Mobile_BBNSB_" + upGradePackageName;
						String ossNodeProtocolFile = RemoteTemplate.getXLSFileFromServer(templatePaths.get(0), FileUtil.getCmCiqDirectory() + File.separator + templatePaths.get(0).replaceAll(".*/", ""), false);
						FileUtil.copyFile(new File(ossNodeProtocolFile), new File(esi_path + File.separator + duInfo.gsm2G.cellList.get(0).nodeName + "_" + new File(ossNodeProtocolFile).getName()));
						String ossNodeProtocolFilePath = esi_path + File.separator + duInfo.gsm2G.cellList.get(0).nodeName + "_" + new File(ossNodeProtocolFile).getName();
						FileUtil.replaceContentInFile(ossNodeProtocolFilePath, "<subjectName>CN=[\\w]+-", "<subjectName>CN=" + duInfo.gsm2G.cellList.get(0).nodeName + "-");
						duInfo.pciSiteObj.setOssNodeProtocolFile(duInfo.gsm2G.cellList.get(0).nodeName + "_" + new File(ossNodeProtocolFile).getName());
					}
				}
				catch (Exception e) {
					Logger.logger.error("calculateEnmId exception! duName=" + duInfo.duName, e);
					Logger.getGmoLogger().printError("Error calculating Enm ID from ossNodeProtocol file for " + duInfo.duName + "!");
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("retrieveOSSNodeProtocol exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error retrieving OSS Node Protocol!");
		}
	}

	
	/**
	 * Function to parse node model and initialize MIM data
	 */
	private void parseNodeModelAndInitMIMData() {
		try {
			// get all software levels
			List<String> softwareLevels = new ArrayList<String>();
			List<String> softwareLevelNew = new ArrayList<String>();	// [06182020]
			for (String site : CommonUtil.getSiteListSet(siteList)) {
				SiteCellObj duInfo = tmoCCR.getDUToDUInfo().get(site);
				if (duInfo != null) {
					String softwareLevel = duInfo.softwareLevel;
				
				softwareLevel = softwareLevel.matches("^\\d.*") ? "L" + softwareLevel : softwareLevel;		// [10292020] For 5G software, add L to make consistent name with MOM shared with LTE. For example 5G "20.Q3" will be searched in software/MOM list as "L20.Q3"
				softwareLevel = softwareLevel.replace(".", "");												// [10292020] L20.Q3 becomes L20Q3
				if (!softwareLevels.contains(softwareLevel) && Arrays.asList(CiqConstants.mimSoftwareLevels).contains(softwareLevel)) {
					softwareLevels.add(softwareLevel);
					Logger.getGmoLogger().printTextWithTimeStamp("Software MIM for " + duInfo.softwareLevel + " will be downloaded.");			// [06182020]
				}
				else if (!softwareLevel.isEmpty() && !softwareLevelNew.contains(softwareLevel) && !softwareLevels.contains(softwareLevel)) {
					softwareLevelNew.add(softwareLevel);
				}
			}}
			// retrieve node model files for all software levels
			if (!softwareLevels.isEmpty()) {
				RemoteTemplate.getParsedMimFiles("TMobile", softwareLevels.toArray(new String[0]));
			}
			if (!softwareLevelNew.isEmpty()) {		// [06182020]
				Logger.getGmoLogger().printError("Software level (" + softwareLevelNew.toString() + ") is not currently supported in GMO. This is required for parameter preservation. Please advise the GMO development team.");
			}
			CMCIQUtil.initDataFromMIMCSV("TMobile");
		}
		catch (Exception e) {
			Logger.logger.error("parseNodeModelAndInitMIMData exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error getting node model and initializing MIM data! " + e.getMessage());
		}
	}

	
	private void generateNSBScripts() throws Exception
	{
		try {
			Logger.getGmoLogger().printHeaderTextWithTimeStamp("Start generating NSB scripts...");

			// generate scripts

			boolean blnEndcScriptsGenerated = false;
			boolean blnGenerate4GNSBL19Q1 = false;
			//generate NR MidBand GLT Scripts
			boolean blnGenerateMidBandGLTScripts = false;

			for (String site : sites) {

				SiteCellObj duInfo = tmoCCR.getDUToDUInfo().get(site);
				String nsbRnDir = null;

				if (duInfo != null) {
					
					if(duInfo.tmoDUInfo.isSetUp1DReconfig && duInfo.duName.startsWith("L")) {
						continue;
					}
					
					// stop script generation if critical errors exist
					if (!duInfo.criticalErrors.isEmpty()) {
						for (String error : duInfo.criticalErrors) {
							Logger.logger.error(error);
							Logger.getGmoLogger().printError(error);
						}
						Logger.logger.error("Critical errors exist! Script generation stopped for " + site + ".");
						Logger.getGmoLogger().printErrorStandard(ErrorCategory.GMO_NOT_SUPPORTED, ErrorSubcategory.USE_CASE_NOT_FOUND,"Critical errors exist! Script generation stopped for " + site + ".");
						continue;
					}

					///////////////////////////////////////////////////
					////	Mid Band Scope
					///////////////////////////////////////////////////
					
					if(duInfo.tmoDUInfo.isMidBandAnchorScope) {
						List<String> rndCellFddList = duInfo.rndCellFddIds;
						List<String> cellFddmatch = new ArrayList<String>();
						String sitePattern = "";
						if(duInfo.duName.matches(".*[\\d]$")) {
							sitePattern = duInfo.duName.replaceAll("[\\d]$", "").replaceAll("^N", "");
						}
						else {
							sitePattern = duInfo.duName.replaceAll("^N", "");
						}
						for(String cellFdd: rndCellFddList) {
						   if(cellFdd.matches(".*" + sitePattern + ".*")) {
							   if(!cellFddmatch.contains(cellFdd)) {
								   cellFddmatch.add(cellFdd);
							   }
						   }
						}
						if(!cellFddmatch.containsAll(rndCellFddList)) {
							blnGenerateMidBandGLTScripts = true;
						}
						else {
							blnGenerateMidBandGLTScripts = false;
						}
					}
					// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
					boolean blnIdleScript = (duInfo.tmoDUInfo.isMidBandAnchorScope && duInfo.is5G && !blnGenerateMidBandGLTScripts) || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope()) || (duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && duInfo.is5G && !duInfo.tmoDUInfo.isMidbandMixedModeBasebandScope);
					blnIdleScript = (duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation && duInfo.isRemovedDU) ? false : blnIdleScript;
					if(blnIdleScript) {
						String strIdleScriptDir = FileUtil.createDirReturnStr(outputDir + File.separator + "IDLE_Cable_Generic");
						moScripts5GNR.generate5GIdleGenericScript(duInfo, strIdleScriptDir + File.separator + duInfo.duName + "_IDLE_Script.mos", "DOS");
					}
					
					///////////////////////////////////////////////////
					////           5G NSB
					///////////////////////////////////////////////////
					if (duInfo.is5G) {

						// if KGET Missing for this site, then generate NSB script
						boolean blnGenerateNSBScripts = (duInfo.kgetFieldReplaceableUnitIds5g.size() == 0) ? true : false;
						blnGenerateNSBScripts = (duInfo.tmoDUInfo.isMidBandAnchorScope && blnGenerateMidBandGLTScripts) ? true : blnGenerateNSBScripts;
						blnGenerateNSBScripts = (duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) ? true : blnGenerateNSBScripts;
						blnGenerateNSBScripts = duInfo.tmoDUInfo.isMidbandMixedModeBasebandScope ? false : blnGenerateNSBScripts;
						blnGenerateNSBScripts = (duInfo.tmoDUInfo.isTDDMixedModeBaseBandScope || duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope) && duInfo.isNewSite ? true : blnGenerateNSBScripts;	// [01092022] Added check for NSB, live status
						blnGenerateNSBScripts = (duInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope && duInfo.isNewSite) ? true : blnGenerateNSBScripts;											// [01102022] Added check for NSB, live status
						blnGenerateNSBScripts = (duInfo.tmoDUInfo.isMidBandTdd2CAddMixedModeBaseBandScope || duInfo.tmoDUInfo.isLiveLowBandAndTdd2CAddMixedModeBaseBandScope) ? false : blnGenerateNSBScripts;
						blnGenerateNSBScripts = (duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope && duInfo.isNewSite) ? true : blnGenerateNSBScripts;																// [01102022] Added check for NSB, live status
						blnGenerateNSBScripts = (duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode() || duInfo.tmoDUInfo.getIsStandAloneMidBandMmbbNode()) ? true : blnGenerateNSBScripts;
						blnGenerateNSBScripts = (duInfo.tmoDUInfo.isMidBandSetUp1DReconfig && duInfo.isNewSite) ? true : blnGenerateNSBScripts;
						blnGenerateNSBScripts = (duInfo.tmoDUInfo.isLowBandSetUp1DReconfig) ? false : blnGenerateNSBScripts;
						blnGenerateNSBScripts = isTestServer && duInfo.tmoDUInfo.isN25MidBandScope && duInfo.isNewSite ? true : blnGenerateNSBScripts;		// [03312022] GMO_TMO-274
						if (blnGenerateNSBScripts) {
							String siteDir = "";

							if(duInfo.tmoDUInfo.isMixedModeBasebandScope || duInfo.tmoDUInfo.isTDDMixedModeBaseBandScope || duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope ||
									duInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope || duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope) {
								if(duInfo.tmoDUInfo.isMixedModeBasebandScope || duInfo.tmoDUInfo.isTDDMixedModeBaseBandScope || duInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope || duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope) {
									siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + "01_" + site + "_BBNSB");
								}
								else if(duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope) {
									if(duInfo.tmoDUInfo.isLowBandMMBBVariation) {
										siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + "01_" + site + "_BBNSB");
									}
									else if(duInfo.tmoDUInfo.isMidBandTddMMBBVariation) {
										siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + "02_" + site + "_BBNSB");
									}
								}
							}
							else if(duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode()) {
								siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + "01_" + site + "_BBNSB");
							}
							else if(duInfo.tmoDUInfo.getIsStandAloneMidBandMmbbNode()) {
								siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + "02_" + site + "_BBNSB");
							}
							else {
								siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + site);
							}
							String nsbDir = FileUtil.createDirReturnStr(siteDir + File.separator + site);

							XMLScripts.generateProjectInfo(duInfo, siteDir + File.separator + "ProjectInfo.xml", "DOS");

							generate5GNR600NodeInfoXml_MTR1923(duInfo, nsbDir + File.separator + "NodeInfo.xml", "DOS");	

							generate5GNRSiteInstallXML(duInfo, nsbDir + File.separator + duInfo.pciSiteObj.SiteInstallationTemplateName, "DOS");

							if (duInfo.tmoDUInfo.isIPSecConfiguration) {
								generate5GNR600SiteBasicNetConf_MTR1923_IPSec(duInfo, nsbDir + File.separator + duInfo.pciSiteObj.SiteBasicTemplateName, "DOS");
							}
							else {
								generate5GNR600SiteBasicNetConf_MTR1923(duInfo, nsbDir + File.separator + duInfo.pciSiteObj.SiteBasicTemplateName, "DOS");
								netconfScripts.generateTN_MTR1923(duInfo, nsbDir + File.separator + duInfo.pciSiteObj.TnTemplateName, "DOS", duInfo.isBBU ? true : false);
							}

							generate5GNRSiteEquipmentNetConf(duInfo, nsbDir + File.separator + duInfo.pciSiteObj.SiteEquipmentTemplateName, "DOS");


							// if you found 5G mmWave sites in the sitelist, and if an RND is present in the input folder, then generate the relevant ENDC scripts.
							boolean blnNeed5GEndcScripts = false;
							if (duInfo.isMmWave) {
								// check if an RND is available in the inputDir
								// locate RND file
								String rndFile = FileUtil.getFilePathFromFolder(inputDir, ".*[Rr][Nn][Dd].*\\.(xls|xlsx|xlsm)$", false);
								if (rndFile == null || rndFile.isEmpty()) {
									blnNeed5GEndcScripts = false;
								}
								else {
									blnNeed5GEndcScripts = true;
								}
							}

							if(duInfo.isNR600 && !duInfo.tmoDUInfo.isMixedModeBasebandScope){
								// Generic IDLE scripts
								// #TC_216
								if((duInfo.kgetCellFddIds.size() == 0) && duInfo.rndCellFddIds.size() > 1) {
									String strIdleScriptDir = FileUtil.createDirReturnStr(outputDir + File.separator + "IDLE_Cable_Generic");
									moScripts5GNR.generate4GIdleGenericScript(strIdleScriptDir + File.separator + "L" + duInfo.duName.substring(1) + "_IDLE_Script.mos", "DOS");
									moScripts5GNR.generate5GIdleGenericScript(duInfo, strIdleScriptDir + File.separator + duInfo.duName + "_IDLE_Script.mos", "DOS");
								}
								else {
									// This is either a GLT site (No cells in kget) or regular carrier add (in which case we don't need IDLE scripts).
								}

								// RiLink scripts
								// #TC_216
								if((duInfo.kgetCellFddIds.size() == 0) && duInfo.rndCellFddIds.size() == 1) {
									// don't generate riLink Script
								}
								else {
									//[11092020] TC_295 - Remove Rilink Folder and include create Rilink part in Carrier Add Script
//									String strRiLinkScriptDir = FileUtil.createDirReturnStr(nsbDir + File.separator + "RiLinks");
//									moScripts5GNR.generate5GCreateRilinkScript_test(duInfo, strRiLinkScriptDir + File.separator + duInfo.duName + "_Create_Rilinks.mos", "DOS");
//									moScripts5GNR.generate5GDeleteAllRilinksScript(duInfo, strRiLinkScriptDir + File.separator + duInfo.duName + "_Delete_Rilinks.mos", "DOS");
								}
							}

							if(duInfo.tmoDUInfo.isMixedModeBasebandScope) {
								//Rilink Folder is no longer needed as its inluded in Carrier Add
//								String strRiLinkScriptDir = FileUtil.createDirReturnStr(nsbDir + File.separator + "RiLinks");
//								moScripts5GNR.generate5GCreateRilinkScript_test(duInfo, strRiLinkScriptDir + File.separator + duInfo.duName + "_Create_Rilinks.mos", "DOS");
//								moScripts5GNR.generate5GDeleteAllRilinksScript(duInfo, strRiLinkScriptDir + File.separator + duInfo.duName + "_Delete_Rilinks.mos", "DOS");
							}

							//[TC_264] TMO Mid Anchor Site
							if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) {
								//[11092020] TC_295 - Remove Rilink Folder and include create Rilink part in Carrier Add Script 
//								String strRiLinkScriptDir = FileUtil.createDirReturnStr(nsbDir + File.separator + "RiLinks");
//								moScripts5GNR.generateMidBandCreateRilinkScript(duInfo, strRiLinkScriptDir + File.separator + "01_" + duInfo.duName + "_Create_Rilinks.mos", "DOS");
//								moScripts5GNR.generateMidBandDeleteAllRilinksScript(duInfo, strRiLinkScriptDir + File.separator + "02_" + duInfo.duName + "_Delete_Rilinks.mos", "DOS");
							}

							if (blnNeed5GEndcScripts && !blnEndcScriptsGenerated) {
								String endcOutputDir = FileUtil.createDirReturnStr(outputDir + File.separator + "ENDC");
								String duNameForKgetLookup = TMO_CommonUtil.getDuNameForKgetLookup(duInfo);		// [08182020] Refactored to method
								String lteEndcCreationDir = FileUtil.createDirReturnStr(endcOutputDir + File.separator + "LTE_ENDC");

								TMO_ENDC_Scripts endcScripts = new TMO_ENDC_Scripts();
								// Generate gNB ENDC Creation Script.
								// [10142021] GMO_TMO-182 Remove gNB_ENDC_Creation for all scopes, is covered in baseline
//								endcScripts.createGnbEndcCreationScript(endcOutputDir + File.separator + "gNB_ENDC_Creation_SWLEVEL.mos", "DOS", tmoCCR.getDUToDUInfo());

								if(duInfo.isMmWave) //TMO_202
								{
									String gnbId = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GNBINFO"), "gNB Name", site, "gNBId");
									// Generate LTE PM Flex Counter Filter Script.
									endcScripts.createmmWaveFlexCounterFilterScript(gnbId,duNameForKgetLookup,lteEndcCreationDir + File.separator + "03_LTE_PmFlexCounterFilter_" + duNameForKgetLookup + "_endc.mos", "DOS");
								}
								else
									// Generate LTE PM Flex Counter Filter Script.
									endcScripts.createPmFlexCounterFilterScript(endcOutputDir + File.separator + "LTE_PmFlexCounterFilter_endc.mos", "DOS");
								boolean blnHasB66Cells = endcScripts.hasB66CellsInLteKget(duNameForKgetLookup);
								// Generate MFBI Activation script.
								if (blnHasB66Cells) {
									endcScripts.createMfbiActivationScript(endcOutputDir + File.separator + "MFBI_Activation-Native B66withoutB12.mos", "DOS", true, duInfo);
								}
								else {
									endcScripts.createMfbiActivationScript(endcOutputDir + File.separator + "MFBI_Activation-B4withoutNativeB66.mos", "DOS", false, duInfo);
								}

								// Generate 3 Rename_Radio_SectorEquipment scripts
								String endcRenameRadioSecEquipOutputDir = "";
								if( duInfo.isMmWave) //TMO_202
								{
									//do Nothing
								}
								else
								{
									endcRenameRadioSecEquipOutputDir = FileUtil.createDirReturnStr(endcOutputDir + File.separator + "01_Rename_Radio_SectorEquipment");
									endcScripts.createRenameRadioSectorEquipmentScript(endcRenameRadioSecEquipOutputDir + File.separator + "Rename_Radio_Sector_Equipment_Site1.mos", "DOS", 1);
									endcScripts.createRenameRadioSectorEquipmentScript(endcRenameRadioSecEquipOutputDir + File.separator + "Rename_Radio_Sector_Equipment_Site2.mos", "DOS", 2);
									endcScripts.createRenameRadioSectorEquipmentScript(endcRenameRadioSecEquipOutputDir + File.separator + "Rename_Radio_Sector_Equipment_Site3.mos", "DOS", 3);
								}
								if( duInfo.isMmWave) //TMO_202 
								{
									// Generate gNB ENDC Creation script
									endcScripts.createmmWaveGnbEndcCreationScript(lteEndcCreationDir + File.separator + "02_gNB_ENDC_Creation_" + duInfo.duName + ".mos", "DOS", duInfo);

								}
								else		// Generate LTE ENDC Creation script
//									moved up ! String lteEndcCreationDir = FileUtil.createDirReturnStr(endcOutputDir + File.separator + "LTE_ENDC");
									endcScripts.createLteEnbEndcCreationScript(lteEndcCreationDir + File.separator + "eNB_ENDC_Creation_" + duNameForKgetLookup.substring(1) + "_endc.mos", "DOS", tmoCCR.getDUToDUInfo());


								// mark that you generated ENDC scripts once
								blnEndcScriptsGenerated = true;
							}

							// Generate RN Scripts if needed.
							boolean blnNeedIPSecRNScripts = duInfo.tmoDUInfo.isIPSecConfiguration;
							if (blnNeedIPSecRNScripts)
							{
								generateTNL19Q1IPSec(duInfo, siteDir + File.separator + duInfo.pciSiteObj.TnTemplateName, "DOS", duInfo.isBBU ? true : false);
								netconfScripts.generateRnEnbfL19Q1(duInfo, siteDir + File.separator + duInfo.pciSiteObj.RnEnbfTemplateName, "DOS", duInfo.isBBU ? true : false);
								netconfScripts.generateRnL19Q1(duInfo, siteDir + File.separator + duInfo.pciSiteObj.RnTemplateName, "DOS", duInfo.isBBU ? true : false);
							}
							if( duInfo.isMmWave) //TMO_202
							{
								BaselineUtil baseline = new BaselineUtil();
								baseline.generate5GmmWaveBaselineScripts(duInfo, nsbDir);
							}
							else {
								if (blnNeed5GEndcScripts) {
									nsbRnDir = FileUtil.createDirReturnStr(siteDir + File.separator + site + File.separator + "RN");			

									// Generate RN Scripts.
									netconfScripts.generate5GRnGnbf(duInfo, nsbRnDir + File.separator + duInfo.pciSiteObj.RnGnbfTemplateName, "DOS");
									netconfScripts.generate5GRnGbrp(duInfo, nsbRnDir + File.separator + duInfo.pciSiteObj.RnGNBRRTemplateName, "DOS");
									netconfScripts.generate5GRnPp(duInfo, nsbRnDir + File.separator + duInfo.pciSiteObj.RnPPTemplateName, "DOS");
									String str06RnCuupFileName = duInfo.pciSiteObj.RnPPTemplateName.replaceAll("06_RN_PP", "06a_RN_CUUP");
									netconfScripts.generate5GRnPpCuup(duInfo, nsbRnDir + File.separator + str06RnCuupFileName, "DOS");

									netconfScripts.generate5GRn(duInfo, nsbRnDir + File.separator + duInfo.pciSiteObj.RnTemplateName, "DOS");
									netconfScripts.generate5GPostInstall(duInfo, nsbRnDir + File.separator + duInfo.pciSiteObj.PostInstallTemplateName, "DOS");
								}

								// [07282020] Insert baseline script for 5G NSB
								BaselineUtil baseline = new BaselineUtil();
								baseline.generate5GNsbBaselineScripts(duInfo, nsbDir);	// [07302020]
								baseline.generateNBIoTBaselineScripts(duInfo, tmoDC.getDuInfoOld(site, sites), nsbDir);
							}
						} // if blnGenerateNsbScripts
					}
					// Change added by sathwik
					else if (duInfo.has2Gsites || duInfo.has3Gsites || duInfo.has2GAnd3GSites) {
						// Generate 2g NSB Script
						String bbnsbPath =outputDir + File.separator + "01_" + duInfo.gsm2G.cellList.get(0).nodeName + "_BBNSB" + File.separator + duInfo.gsm2G.cellList.get(0).nodeName;
						//String basebandOutputDirectory = outputDir + File.separator + "Baseband" + File.separator + site.toUpperCase();
						//new File(basebandOutputDirectory).mkdirs();
						SimpleDateFormat sdf = new  SimpleDateFormat("yyyy_MM_dd'T'HH_mm_ss'Z'");
						//Script generation for ENM_AP
						//String enmApOutputDirectory = outputDir + File.separator + "ENM_AP" + File.separator + site.toUpperCase();
						String enmApDirectory = outputDir + File.separator + "01_" + duInfo.gsm2G.cellList.get(0).nodeName + "_BBNSB";
						File file =new File(bbnsbPath);
						if(!file.exists()) {
							file.mkdirs();
						}
						XMLScripts.generate2GAnd3GProjectInfo(duInfo, enmApDirectory + File.separator + "ProjectInfo.xml", "DOS");
						
														
						String basebandSiteBasicFileName =  "01_SiteBasic_TMO_G+W_NSB_Production_Tmobile_" + sdf.format(new Date()) + ".xml";
						netconfScripts.generate2GAnd3GSiteBasic(duInfo,bbnsbPath + File.separator + basebandSiteBasicFileName,"DOS");
						
						
						String basebandSiteEquipmentFileName = "02_SiteEquipment_TMO_G+W_NSB_Production_Tmobile_" + sdf.format(new Date()) + ".xml";
						netconfScripts.generate2GAnd3GSiteEquipment(duInfo, bbnsbPath + File.separator + basebandSiteEquipmentFileName, "DOS");

						//Baseband 
						String basebandSiteInstallationFileName = "SiteInstallation_TMO_G+W_NSB_Production_Tmobile_" + sdf.format(new Date()) + ".xml";
						XMLScripts.generate2GAnd3GSiteInstallation(duInfo, bbnsbPath + File.separator + basebandSiteInstallationFileName, "DOS");
						
						String basebandTransportFileName = "03_TN_TMO_G+W_NSB_Production_Tmobile_" + sdf.format(new Date()) + ".xml";
						netconfScripts.generate2GAnd3GTransport(duInfo, bbnsbPath + File.separator + basebandTransportFileName, "DOS");
						
						duInfo.pciSiteObj.SiteBasicTemplateName = basebandSiteBasicFileName;
						duInfo.pciSiteObj.SiteEquipmentTemplateName = basebandSiteEquipmentFileName;
						duInfo.pciSiteObj.SiteInstallationTemplateName = basebandSiteInstallationFileName;
						
						xmlScripts.generate2GAnd3GNodeInfo(duInfo, bbnsbPath + File.separator + "NodeInfo.xml", "DOS", basebandTransportFileName);
						
						BaselineUtil baseline = new BaselineUtil();
						Set<String> physicalSites= CommonUtil.convertSiteListToArrayList(siteList).stream().collect(Collectors.toSet());
						baseline.generate2GAnd3GBaseLine(outputDir,tmoCCR,physicalSites);
						generateAdd_controlling_BSC_and_RNC(duInfo,enmApDirectory);
					}
					
					else {
						///////////////////////////////////////////////////
						////           4G NSB Block
						///////////////////////////////////////////////////
						blnGenerate4GNSBL19Q1 = CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "19.Q1");		// [03082021] Updated to generic check of software level
						String siteDir = "";
						String nsbSiteDir = "";
						String nsbDir = "";
						// [euttsaw] 3/18/2020: need a consolidated trigger for 4G NSB scripts
						if (!duInfo.tmoDUInfo.isMixedModeBasebandScope && !duInfo.tmoDUInfo.isCPRIRemappingProject 
								&& !(duInfo.tmoDUInfo.isNewSCUConfiguration || duInfo.tmoDUInfo.isExistingSCUConfiguration) &&
								!duInfo.tmoDUInfo.isTDDMixedModeBaseBandScope && !duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope && 
								!duInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope && !duInfo.tmoDUInfo.isMidBandTdd2CAddMixedModeBaseBandScope &&
								!duInfo.tmoDUInfo.isLiveLowBandAndTdd2CAddMixedModeBaseBandScope && !duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope) {
							if ((!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) || 
								(!duInfo.getSiteObj().isIs4gAnchor() && !duInfo.tmoDUInfo.isTDDNode()))	{	// [12082020] TC_368 Generate these lines for TDD, not FDD nodes
								///////////////////////////////////////////////////
								////           4G NSB Direct
								///////////////////////////////////////////////////
								siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + site);
								nsbDir = FileUtil.createDirReturnStr(siteDir + File.separator + "01_NSB_NO_SECTOR_" + duInfo.softwareLevel);
								nsbSiteDir = FileUtil.createDirReturnStr(nsbDir + File.separator + site);
								// cleanup folder
								FileUtil.removeFilesInFolder(nsbSiteDir, ".*\\.xml");

								// generate scripts
								XMLScripts.generateProjectInfo(duInfo, nsbDir + File.separator + "ProjectInfo.xml", "DOS");
								if (blnGenerate4GNSBL19Q1) {
									xmlScripts.generateNodeInfoL19Q1(duInfo, nsbSiteDir + File.separator + "NodeInfo.xml", "DOS");
									netconfScripts.generateSiteBasicL19Q1(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.SiteBasicTemplateName, "DOS");
									netconfScripts.generateSiteEquipmentNoSectorL19Q1(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.SiteEquipmentTemplateName, "DOS", false);
									netconfScripts.generateTNL19Q1(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.TnTemplateName, "DOS", duInfo.isBBU ? true : false);
									// No changes for SiteInstallation file between L17/L18/L19.., per Ada
									XMLScripts.generateSiteInstallation(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.SiteInstallationTemplateName, "DOS");
									netconfScripts.generateRnEnbfL19Q1(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.RnEnbfTemplateName, "DOS", duInfo.isBBU ? true : false);
									netconfScripts.generateRnL19Q1(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.RnTemplateName, "DOS", duInfo.isBBU ? true : false);
								}
								else {
									XMLScripts.generateNodeInfo(duInfo, nsbSiteDir + File.separator + "NodeInfo.xml", "DOS");
									netconfScripts.generateSiteBasic(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.SiteBasicTemplateName, "DOS");
									netconfScripts.generateSiteEquipmentNoSectorTmo(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.SiteEquipmentTemplateName, "DOS", false);
									xmlScripts.generateTN(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.TnTemplateName, "DOS", duInfo.isBBU ? true : false);
									XMLScripts.generateSiteInstallation(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.SiteInstallationTemplateName, "DOS");
									XMLScripts.generateRnEnbf(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.RnEnbfTemplateName, "DOS", duInfo.isBBU ? true : false);
									XMLScripts.generateRn(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.RnTemplateName, "DOS", duInfo.isBBU ? true : false);
								}
							}
							else {
								///////////////////////////////////////////////////
								////           4G NSB Mid Band Anchor Scope
								///////////////////////////////////////////////////
								String siteNameTrimmed = site.replaceAll("^[A-Z]", "").replaceAll("[\\d]{1}$", "");
								// nsbDir = FileUtil.createDirReturnStr(outputDir + File.separator + "LTE_Node" + File.separator + siteNameTrimmed + File.separator + "01_NSB_B41_Scripts_" + siteNameTrimmed + "" + File.separator + site);
								nsbDir = FileUtil.createDirReturnStr(outputDir + File.separator + "01_NSB_B41_Scripts_" + siteNameTrimmed + "" + File.separator + site);
								nsbSiteDir = FileUtil.createDirReturnStr(nsbDir + File.separator + site);

								XMLScripts.generateProjectInfo(duInfo, nsbDir + File.separator + "ProjectInfo.xml", "DOS");
								xmlScripts.generateNodeInfoL19Q1(duInfo, nsbSiteDir + File.separator + "NodeInfo.xml", "DOS");
								netconfScripts.generateSiteBasicL19Q1(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.SiteBasicTemplateName, "DOS");
								netconfScripts.generateSiteEquipmentNoSectorL19Q1(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.SiteEquipmentTemplateName, "DOS", false);
								netconfScripts.generateTNL19Q1(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.TnTemplateName, "DOS", duInfo.isBBU ? true : false);
								XMLScripts.generateSiteInstallation(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.SiteInstallationTemplateName, "DOS");
								netconfScripts.generateRnEnbfL19Q1(duInfo, nsbSiteDir + File.separator + duInfo.pciSiteObj.RnEnbfTemplateName, "DOS", duInfo.isBBU ? true : false);
//								//[11092020] - Remove Rilink Folder as create portion is included in Carrier Add 
//								String RilinkDir = FileUtil.createDirReturnStr(nsbSiteDir + File.separator + "RiLinks");
//								netconfScripts.create4GRilinks(duInfo, RilinkDir + File.separator + site + "_Create_Rilinks.mos", "DOS");
							}
						}
						
						if (duInfo.isNewSite) {	// [08032020] Insert baseline script for 4G NSB
							String highLevelScope = "4G";
							String secondLevelScope = "NSB";
							String baselineScriptDir = FileUtil.createDirReturnStr(nsbDir + File.separator + "Baseline");
							BaselineUtil baseline = new BaselineUtil();
							baseline.generate4GNsbBaseline(duInfo, highLevelScope, secondLevelScope, baseline.baseline4GNsbMap(), baselineScriptDir);

							baseline.generateNBIoTBaselineScripts(duInfo, tmoDC.getDuInfoOld(site, sites), nsbDir);
						}
					}
				}
				else {
					Logger.getGmoLogger().printWarning("Missing data for " + site + ". Scripts not generated.");
				}
			}
			Logger.getGmoLogger().printHeaderTextWithTimeStamp("Finished generating NSB Scripts.");
		}
		catch (Exception e) {
			Logger.logger.error("generateNSBScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating NSB scripts! " + e.getMessage());
		}
	}

	
	private void generateAdd_controlling_BSC_and_RNC(SiteCellObj duInfo,String bbsPath) {
		String eol = StringUtil.getEOL("DOS");
		Logger.getGmoLogger().printTextWithTimeStamp("creating 2G and 3G base line script");
		StringBuilder sb = new StringBuilder();
		String bsc=duInfo.gsm2G.BSCName;
		
		sb.append("cmedit get NetworkElement=" + duInfo.gsm2G.cellList.get(0).nodeName).append(eol);
		if(duInfo.wcdma3G!=null && duInfo.wcdma3G.cellList!=null && !duInfo.wcdma3G.cellList.isEmpty()) {
			sb.append("cmedit set NetworkElement=" + duInfo.gsm2G.cellList.get(0).nodeName + " controllingRnc=\"NetworkElement=" + duInfo.wcdma3G.rncName + "\"").append(eol);
		}
		if(duInfo.gsm2G.BSCName!=null && !duInfo.gsm2G.BSCName.isEmpty()) {
			bsc=bsc.replace("BSC", "BS");
			sb.append("cmedit set NetworkElement=" + duInfo.gsm2G.cellList.get(0).nodeName + " controllingBsc=\"NetworkElement=" + bsc + "\"").append(eol);
		}
		sb.append("cmedit get NetworkElement=" + duInfo.gsm2G.cellList.get(0).nodeName).append(eol);
		String fileName=bbsPath + File.separator + duInfo.gsm2G.cellList.get(0).nodeName + "_Add_controlling_BSC_and_RNC.txt";
		FileUtil.writeToFile(sb, fileName);
	}

	
	/**
	 * 
	 */
	protected void basicValidationOfOutput()
	{
		/*** Basic validation of output ***/
		ScriptValidation sv = new ScriptValidation();
		if (SystemConstants.userSignum.equalsIgnoreCase("ejashsi") || SystemConstants.userSignum.equalsIgnoreCase("eshinai") || GlobalConst.isS2G || GlobalConst.isTestCase() || (isMDUScope) || (ignoreValidationDialog)) {
			sv.validateOutput(outputDir, false, null);
		}
		else {
			sv.validateOutput(outputDir, true, null);
		}
	}
	
	
	private void generate5GCarrierAddScripts() throws Exception
	{
		try {
			Logger.getGmoLogger().printHeaderTextWithTimeStamp("Start generating 5G Carrier Add scripts...");
			//generate NR MidBand GLT Scripts
			boolean blnGenerateMidBandGLTScripts = false;
			for (String site : sites) {

				SiteCellObj duInfo = tmoCCR.getDUToDUInfo().get(site);
				String duNameForKgetLookup = TMO_CommonUtil.getDuNameForKgetLookup(duInfo);	// [08182020] Refactored to method
				
				if (duInfo != null) {

					// stop script generation if critical errors exist
					if (!duInfo.criticalErrors.isEmpty()) {
						for (String error : duInfo.criticalErrors) {
							Logger.logger.error(error);
							Logger.getGmoLogger().printError(error);
						}
						Logger.logger.error("Critical errors exist! Script generation stopped for " + site + ".");
						Logger.getGmoLogger().printErrorStandard(ErrorCategory.GMO_NOT_SUPPORTED, ErrorSubcategory.USE_CASE_NOT_FOUND,"Critical errors exist! Script generation stopped for " + site + ".");
						continue;
					}
					
					///////////////////////////////////////////////////
					////	Mid Band Scope
					///////////////////////////////////////////////////
					if(duInfo.tmoDUInfo.isMidBandAnchorScope) {
						List<String> rndCellFddList = duInfo.rndCellFddIds;
						List<String> cellFddmatch = new ArrayList<String>();
						String sitePattern = "";
						if(duInfo.duName.matches(".*[\\d]$")) {
							sitePattern = duInfo.duName.replaceAll("[\\d]$", "").replaceAll("^N", "");
						}else {
							sitePattern = duInfo.duName.replaceAll("^N", "");
						}

						for(String cellFdd: rndCellFddList) {
						   if(cellFdd.matches(".*" + sitePattern + ".*")) {
							   if(!cellFddmatch.contains(cellFdd)) {
								   cellFddmatch.add(cellFdd);
							   }
						   }
						}
						if(!cellFddmatch.containsAll(rndCellFddList)) {
							blnGenerateMidBandGLTScripts = true;
						}else {
							blnGenerateMidBandGLTScripts = false;
						}
					}

					if (duInfo.is5G) {

						Logger.getGmoLogger().printHeaderTextWithTimeStamp("Generating for " + duInfo.duName + "...");

						// if RND present and site present in RND, then generate Carrier Add script
						boolean blnGenerateCarrierAddScripts = (duInfo.rndFieldReplaceableUnitIds5g.size() > 0) ? true : false;
						blnGenerateCarrierAddScripts = (duInfo.tmoDUInfo.isMixedModeBasebandScope) ? false : blnGenerateCarrierAddScripts;
						blnGenerateCarrierAddScripts = (duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) ? true : blnGenerateCarrierAddScripts;
						blnGenerateCarrierAddScripts = duInfo.tmoDUInfo.isMidbandMixedModeBasebandScope? false : blnGenerateCarrierAddScripts;
						blnGenerateCarrierAddScripts = (duInfo.tmoDUInfo.isTDDMixedModeBaseBandScope || duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope)? false : blnGenerateCarrierAddScripts;
						blnGenerateCarrierAddScripts = (duInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope)? false : blnGenerateCarrierAddScripts;
						blnGenerateCarrierAddScripts = duInfo.tmoDUInfo.isIPSecConfiguration ? false : blnGenerateCarrierAddScripts;
						blnGenerateCarrierAddScripts = (duInfo.tmoDUInfo.isMidBandTdd2CAddMixedModeBaseBandScope || duInfo.tmoDUInfo.isLiveLowBandAndTdd2CAddMixedModeBaseBandScope) ? false : blnGenerateCarrierAddScripts;
						blnGenerateCarrierAddScripts = (duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope) ? false : blnGenerateCarrierAddScripts;
						blnGenerateCarrierAddScripts = (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope()) ? true : blnGenerateCarrierAddScripts;
						blnGenerateCarrierAddScripts = (duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode() || duInfo.tmoDUInfo.getIsStandAloneMidBandMmbbNode()) ? false : blnGenerateCarrierAddScripts;
						blnGenerateCarrierAddScripts = (duInfo.tmoDUInfo.isSetUp1DReconfig) ? false : blnGenerateCarrierAddScripts;
						
						String siteDir = "";
						String caDir = "";
						String ngsDir = "";
						
						if(blnGenerateCarrierAddScripts) {
							if(duInfo.tmoDUInfo.isMidBandAnchorScope && !blnGenerateMidBandGLTScripts || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
								caDir = FileUtil.createDirReturnStr(outputDir + File.separator + "CarrierAdd");
							}
							else if(blnGenerateMidBandGLTScripts){
								//do nothing
							}
							else {
								siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + site);
								caDir = FileUtil.createDirReturnStr(siteDir + File.separator + "CarrierAdd");
								ngsDir = FileUtil.createDirReturnStr(outputDir + File.separator + "NGS");
							}
							
							
							String caBulkDir = "";
							String lteEndcCreationDir ="";

							// [eshinai: 070119] If the config type in RND matches '_m28a' or '_m39a' then it is MTR19.21. Only generate one Carrier Add script.

							if(duInfo.designConfig.matches(".*(_[mM]28[aA]|_[mM]39[aA]).*"))
							{
								generateCarrierAddCCScript01_MTR1921(duInfo, caDir + File.separator + "01_" + duInfo.duName + "_" + duInfo.designConfig + "_Carr_Add.mos", "DOS");
							
							}else if((duInfo.tmoDUInfo.isMidBandAnchorScope && !blnGenerateMidBandGLTScripts) || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
								if ((duInfo.kgetCellFddIds.size() == 0) && (duInfo.rndCellFddIds.size() > 1 || (duInfo.rndCellFddIds.size() == 1) )) {
									generateCarrierAdd01Script(duInfo, caDir + File.separator + "01_" + duInfo.duName + "_CarrierAdd.mos", "DOS");
									if(duInfo.rndCellFddIds.size() > 1) {
										if( duInfo.isMmWave){ //TMO_202
											tmoCCR.generateMmWaveNRCAIntrafreqIntragnbRelation( caDir + File.separator + "02_" + duInfo.duName + "_mmWave_NRCA_Intrafreq-intragnb-relation_MultiSector.mos");
										}
										else
										//generateIntraFreqInterGnbRelationScript(duInfo, caDir + File.separator + "02_" + duInfo.duName + "_Intrafreq-intragnb-relation.mos", "DOS");
										// Updated to use new, common call in this class
										tmoCCR.generateIntraFreqInterGnbRelationScriptFunction(duInfo, caDir + File.separator + "02_" + duInfo.duName + "_Intrafreq-intragnb-relation.mos");
									}
									generatePTPSlaveConfigurationScript(duInfo, caDir + File.separator + "03_" + duInfo.duName + "_PTP_Slave_Configuration.mos", "DOS");	//TC_376 -> changed "02" to "03"
								}

								// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
								generateN41ConsolidationScripts(site, caDir, duInfo);

								// TC_313 - Additional script for NR600 carrieradd for Philly market
								generateNR600CPAScript(duInfo, caDir + File.separator + "5G_NSA_SA_Coexistence_Rev4.mos");

							    TMO_ENDC_Scripts endcScripts = new TMO_ENDC_Scripts();
								String endcOutputDir = FileUtil.createDirReturnStr(outputDir + File.separator + "ENDC");

								ArrayList<String> lstDistinctLteSiteNameFromRnd = TMODataCollector.getDistinctLteSiteNamesForLteSiteFromRnd(duNameForKgetLookup);
								// [12102020]
								lstDistinctLteSiteNameFromRnd = tmoCCR.rndLteSitesFromSiteName;	// [12102020] Added calculation of list in data collection of tmoCCR

								ArrayList<String> lstDistinctLteSiteNamesForThis5GSite = TMODataCollector.getDistinctLteSiteNamesFor5GSite(duNameForKgetLookup);
								String lteFddSiteNameString = TMODataCollector.getDistinctLteSiteNamesMatchesFDDType(duNameForKgetLookup);
								for(String currLteSiteName : lstDistinctLteSiteNamesForThis5GSite) {
									// get the list of cellFddNames for this LTE site from its kget
									ArrayList<String> lstLteCellFddNamesForThisLteSite = TMODataCollector.getDistinctCellFddNamesForLteSite(currLteSiteName);
									if(lstLteCellFddNamesForThisLteSite != null && lstLteCellFddNamesForThisLteSite.size() > 0) {
										// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
										boolean newSiteOrNon6449Node = duInfo.tmoDUInfo.triggerAir6449SwapScripts || (duInfo.tmoDUInfo.radioTypeSet.toString().matches(".*6449.*") && !duInfo.isNewSite) ? false : true; 	// [08202021] GMO_TMO-152 do not trigger scripts, data already exists in node, if live NR node has or will have AIR6449
										newSiteOrNon6449Node = duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation ? false : newSiteOrNon6449Node;
										lteEndcCreationDir = FileUtil.createDirReturnStr(endcOutputDir + File.separator + "LTE_ENDC");
										if(!tmoDC.checkIf4SecConfig(duInfo) && newSiteOrNon6449Node) {
											endcScripts.createLteEnbEndcCreationScript(lteEndcCreationDir + File.separator + "01_eNB_ENDC_Creation_LTE_Multisite_" + duInfo.duName + "_endc.mos", "DOS", tmoCCR.getDUToDUInfo(), currLteSiteName, lstLteCellFddNamesForThisLteSite, site);	// TC_376 added "01_"
										}
										for(String LteSiteName: lstDistinctLteSiteNameFromRnd) {
											if(LteSiteName.matches(lteFddSiteNameString.replaceAll("_", "|"))) {
												boolean blnTriggerCreateLtePmFlexCounterScript = true;
												// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
												blnTriggerCreateLtePmFlexCounterScript = (duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation && duInfo.isRemovedDU) ? false : blnTriggerCreateLtePmFlexCounterScript;
												//TC_322
												if (blnTriggerCreateLtePmFlexCounterScript) {
													endcScripts.createLtePmFlexCounterScript(lteEndcCreationDir + File.separator + "03_" + LteSiteName + "_LTE_PmFlexCounterFilter_" + duInfo.duName + "_endc.mos", "DOS", LteSiteName, duInfo, tmoCCR.getDUToDUInfo());	// TC_376 added "03_"
												}

												// GMO_TMO-131 [08092021]
												SiteCellObj lteDuInfo = tmoCCR.getDUToDUInfo().get(LteSiteName);	// ok to be null
//												if (/*lteDuInfo != null) {
												for (Entry<String, SiteCellObj> duTemp: tmoCCR.getDUToDUInfo().entrySet())	{
													if (duTemp.getValue().tmoDUInfo.triggerAir6449SwapScripts) {				// A N41 node in the site has an antenna swap
														// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
														String prefixDeleteCellRelationScript = duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation ? "01_" : "00_";
														tmoCCR.generateDeleteCellRelationScript(lteDuInfo, LteSiteName, duTemp.getValue().enbId, duInfo.subNetwork, lteEndcCreationDir + File.separator + prefixDeleteCellRelationScript + lteFddSiteNameString + "_Delete_Relation_CellRelation.mos");
														break;
													}
												}
												//
											}
										}
										if (newSiteOrNon6449Node) {		// [08202021] GMO_TMO-152
											// [10142021] GMO_TMO-182 Remove gNB_ENDC_Creation for all scopes, is covered in baseline
//											endcScripts.createLteGnbEndcCreationScript(duInfo, lteEndcCreationDir + File.separator + "02_gNB_ENDC_Creation_" + duInfo.duName + ".mos", "DOS", duInfo.duName);		// TC_376 added "02_"
										}
//										endcScripts.generateNodeGutranCellRelationScript(duInfo, lteEndcCreationDir + File.separator + "Node_GutranCellRelation_" + LteSiteNameString + ".mos", "DOS");
										// Updated to use new, common call in this class
										boolean blnTriggerCreateNodeGutranCellRelationScript = true;
										// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
										blnTriggerCreateNodeGutranCellRelationScript = (duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation && duInfo.isRemovedDU) ? false : blnTriggerCreateNodeGutranCellRelationScript;
										if (blnTriggerCreateNodeGutranCellRelationScript) {
											tmoCCR.generateNodeGutranCellRelationScriptFunction(duInfo, duInfo, lteEndcCreationDir + File.separator + "04_" + lteFddSiteNameString + "_Node_GutranCellRelation_" + duInfo.duName + ".mos");	// TC_376 added "04_"
										}
									}
								}
								
								//TC_295
								if(tmoDC.checkIf4SecConfig(duInfo)) {
									if(duInfo.kgetCellFddIds.size() == 0 && duInfo.rndCellFddIds.size() == 3) {
										endcScripts.createCombinedLteEnbEndcCreationScript(lteEndcCreationDir + File.separator + "eNB_ENDC_Creation_LTE_Multisite_endc.mos", "DOS", tmoCCR.getDUToDUInfo(), site); 
									}else if(duInfo.kgetCellFddIds.size() == 0 && duInfo.rndCellFddIds.size() == 1) {
										//do not generate 2nd Node 
									}
								}
								
								// GMO_TMO-131 [08092021]
								if (duInfo.tmoDUInfo.triggerAir6449SwapScripts) {
									// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
									String prefixDeleteCellRelationScript = duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation ? "01_" : "00_";
									String prefixNrBwPwrRiportRilinkMosScript = duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation ? "01b_" : "01a_";
									tmoCCR.generateDeleteCellRelationScript(duInfo, duInfo.duName, duInfo.enbId, duInfo.subNetwork, caDir + File.separator + prefixDeleteCellRelationScript + duInfo.duName + "_Delete_Relation_CellRelation.mos");
									tmoCCR.generateNrBwPwrRiportRilinkMosScript(duInfo, caDir + File.separator + prefixNrBwPwrRiportRilinkMosScript + duInfo.duName + "_NR_arfcn_Bandwidth_Power_Riport_Rilink_Update.mos");//[09012021 - ezrxxsu] Updated the file sequence.

									// GMO_TMO-152 [08202021]
									tmoCCR.generateIntraFreqInterGnbRelationScriptFunction(duInfo, caDir + File.separator + "02_" + duInfo.duName + "_Intrafreq-intragnb-relation.mos");
								}
								
								//TC_369 [ezrxxsu]
								if(tmoDC.triggerGenericNRToLTERelationUpdated(duInfo)) {
									tmoCCR.generateNRToLTERelationScript(duInfo.duName, caDir + File.separator + "04_" + duInfo.duName + "_NR_To_LTE_Relation.mos"); //TC_376 added "04" in file name.
								}
								
								//TC_372 [ezrxxsu]
								if(duInfo.tmoDUInfo.triggerNR2NRRelationScript) {
									String sourceNode = "N41";
									String targetNode = "N71";
									tmoCCR.generateNRToNRRelationScript(duInfo, caDir + File.separator + "05_" + duInfo.duName + "_NR41_To_NR71_Relation.mos", sourceNode, targetNode);
								}
								else {
									//[05112021 - exrxxsu] - Remove test server flag only when 21.Q1 is GAed
									// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
									boolean blnGenerateMobilityParameters = CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q1") ? true : false;
									blnGenerateMobilityParameters = (duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation && duInfo.isRemovedDU) ? false : blnGenerateMobilityParameters;
									if (blnGenerateMobilityParameters) {	
										String mobilityParameterScript = caDir + File.separator + "05_" + duInfo.duName + "_Mobility_Parameter.mos";
										generateMobilityParameterChangeScript(duInfo, mobilityParameterScript, "UNIX");
									}
								 }
							}
							else
							{
								if(duInfo.isNR600)
								{
									boolean blnIs4SecReconfigScope = false;

									// #TC_216
									// check how many cells are present in the kget.
									// If there are 4 or more Cells in the 5G Kget and this site has 3 cells in the RND, then this is a reconfiguration scope (move the 4th cell to a new site).

									if((duInfo.kgetCellFddIds.size() >= 4) && (duInfo.rndCellFddIds.size() == 3)) {
										blnIs4SecReconfigScope = true;
									}
									else {
										// As of Oct 14 2019, all 5G kgets are supposed to have 4 sectors in them because there is a dependency on this when creating the 02_Carrier_add scripts.
										// Notify the user that this is a non-standard kget and ask them to review the scripts.
										// Logger.getGmoLogger().printError("5G Kget has less than 4 cells. This is non-standard. Please check the script outputs for site [" + duInfo.duName + "]");
										// [eshinai:Oct-14-19]check the number of cells for this site in the RND. If it has only one cell, then assume that this is the new 2nd node
										if((duInfo.kgetCellFddIds.size() == 0) && (duInfo.rndCellFddIds.size() == 1)) {
											generate5GNR600CarrierAdd02Script(duInfo, caDir + File.separator + "02_" + duInfo.duName + "_CarrierAdd_NR600.mos", "DOS");
										}
										else if ((duInfo.kgetCellFddIds.size() == 0) && (duInfo.rndCellFddIds.size() > 1)) {
											// this means this is a Green Light Tested (GLT) site. Generate the regular 01_Carrier_add script.
											generateCarrierAdd01Script(duInfo, caDir + File.separator + "01_" + duInfo.duName + "_CarrierAdd_NR600.mos", "DOS");

											// TC_313 - Additional script for NR600 carrieradd for Philly market
											generateNR600CPAScript(duInfo, caDir + File.separator + "5G_NSA_SA_Coexistence_Rev4.mos");

											// generateIntraFreqInterGnbRelationScript(duInfo, caDir + File.separator + "02_" + duInfo.duName + "_Intrafreq-intragnb-relation.mos", "DOS");
											// Updated to use new, common call in this class
											tmoCCR.generateIntraFreqInterGnbRelationScriptFunction(duInfo, caDir + File.separator + "02_" + duInfo.duName + "_Intrafreq-intragnb-relation.mos");
											
											//TC_357
											if(tmoDC.triggerGenericNRToLTERelationUpdated(duInfo)) {
												tmoCCR.generateNRToLTERelationScript(duInfo.duName, caDir + File.separator + "04_" + duInfo.duName + "_NR_To_LTE_Relation.mos"); //TC_376 added "04" in file name.
											}
											
											//TC_372 [ezrxxsu]
											if(duInfo.tmoDUInfo.triggerNR2NRRelationScript) {
												String sourceNode = "N71";
												 String targetNode = "N41";
												tmoCCR.generateNRToNRRelationScript(duInfo, caDir + File.separator + "05_" + duInfo.duName + "_NR71_To_NR41_Relation.mos", sourceNode, targetNode);
											}
											else {
												//[05112021 - exrxxsu] - Remove test server flag only when 21.Q1 is GAed
												if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q1")) {	
													String mobilityParameterScript = caDir + File.separator + "05_" + duInfo.duName + "_Mobility_Parameter.mos";
													generateMobilityParameterChangeScript(duInfo, mobilityParameterScript, "UNIX");
												}
											 }
										}
										else {
											Logger.getGmoLogger().printError("Unsupported number of cells in RND and KGet. This is non-standard. Please check the script outputs for site [" + duInfo.duName + "]");
										}
									}

									if(blnIs4SecReconfigScope) {
										// generate the Carrier Add Script for reconfig scope
										generate5GNR600DeltaDeleteScript(duInfo, caDir + File.separator + "01_" + duInfo.duName + "_Delta_Delete_NR600.mos", "DOS");
									}
									else {
										// you must have already created a Carrier Add script, or thrown an error saying Unsupported Number of Cells.
									}

									// #TC_216
									if((duInfo.kgetCellFddIds.size() == 4) && (duInfo.rndCellFddIds.size() == 3)) {
										// first node. No need of RiLink script for this node.
									}
									else if ((duInfo.kgetCellFddIds.size() == 0) && (duInfo.rndCellFddIds.size() == 1)) {
										// Second node. No need of RiLink script for this node.
									}
									else {
										// not sure what scope this is. Go ahead and generate it. Engr should be able to figure out what to do. 
										// [10232020] TODO May turn off for MMBB var 2/3, but should be no harm. Rilinks generated in another script for MMBB 2/3. Keep for now, per Rathin
										generate5GNR600RiLinkScriptForNGS(duInfo, ngsDir + File.separator + "02_" + duInfo.duName + "_Create_RiLinks_NR600.mos", "DOS");
									}

									// Generate Script: LTE ENDC Creation
									TMO_ENDC_Scripts endcScripts = new TMO_ENDC_Scripts();
									String endcOutputDir = FileUtil.createDirReturnStr(outputDir + File.separator + "ENDC");

									// get the list of CellFdd names from the LTE Kget and map them to their corresponding LTE DU Name.
									// Note that you may get something like 3 'L' cells and '3' B cells (i.e. AAS sites). 
									// For such cases, you need two separate ENDC scripts, one for each LTE site with its corresponding cell names

									// 1 get distinct LTE node names from the kget that match this 5G site's name
									ArrayList<String> lstDistinctLteSiteNamesForThis5GSite = TMODataCollector.getDistinctLteSiteNamesFor5GSite(duNameForKgetLookup);
									for(String currLteSiteName : lstDistinctLteSiteNamesForThis5GSite) {
										// get the list of cellFddNames for this LTE site from its kget
										ArrayList<String> lstLteCellFddNamesForThisLteSite = TMODataCollector.getDistinctCellFddNamesForLteSite(currLteSiteName);
										if(lstLteCellFddNamesForThisLteSite != null && lstLteCellFddNamesForThisLteSite.size() > 0) {
											lteEndcCreationDir = FileUtil.createDirReturnStr(endcOutputDir + File.separator + "LTE_ENDC");
											// #TC_216
											if((duInfo.kgetCellFddIds.size() == 4) && (duInfo.rndCellFddIds.size() == 3)) {
												// first node. no need of enb_ENDC script for this site.
											}
											else {
												if(!tmoDC.checkIf4SecConfig(duInfo)) {
													endcScripts.createLteEnbEndcCreationScript(lteEndcCreationDir + File.separator + "eNB_ENDC_Creation_LTE_Multisite_" + duInfo.duName + "_endc.mos", "DOS", tmoCCR.getDUToDUInfo(), currLteSiteName, lstLteCellFddNamesForThisLteSite, site); 	// TC_376 added "01_" -> removed
												}
											}
											
											//TC_322
											endcScripts.createLtePmFlexCounterScript(lteEndcCreationDir + File.separator + "LTE_PmFlexCounterFilter_" + currLteSiteName + "_endc.mos", "DOS", currLteSiteName, duInfo, tmoCCR.getDUToDUInfo());	// TC_376 Added "03_" -> removed
											// #TC_216
											// if this site has 4 sectors in the kget, no need to generate gNB Endc script
											if(duInfo.kgetCellFddIds.size() == 4) {
												// don't generate.
											}
											else {
												// [10142021] GMO_TMO-182 Remove gNB_ENDC_Creation for all scopes, is covered in baseline
//												endcScripts.createLteGnbEndcCreationScript(duInfo, lteEndcCreationDir + File.separator + "gNB_ENDC_Creation_" + duInfo.duName + ".mos", "DOS", duInfo.duName);	//TC_376 Added "02_" -> removed
											}

//											endcScripts.generateNodeGutranCellRelationScript(duInfo, lteEndcCreationDir + File.separator + "Node_GutranCellRelation_" + currLteSiteName + ".mos", "DOS");
											// Updated to use new, common call in this class
											tmoCCR.generateNodeGutranCellRelationScriptFunction(duInfo, duInfo, lteEndcCreationDir + File.separator + "Node_GutranCellRelation_" + currLteSiteName + ".mos");  	//TC_376 Added "04_" -> removed
										}
									}
									
									//TC_295 Merge ENDC scripts for 4 sector configs
									if(tmoDC.checkIf4SecConfig(duInfo)) {
										if(duInfo.kgetCellFddIds.size() == 0 && duInfo.rndCellFddIds.size() == 3) {
											endcScripts.createCombinedLteEnbEndcCreationScript(lteEndcCreationDir + File.separator + "eNB_ENDC_Creation_LTE_Multisite_endc.mos", "DOS", tmoCCR.getDUToDUInfo(), site); 
										}else if(duInfo.kgetCellFddIds.size() == 0 && duInfo.rndCellFddIds.size() == 1) {
											//do not generate 2nd Node 
										}
									}
									
									// Generate Script: LTE NGS Scripts - [eusxjas - 080519] 
									String [] siteGroup = new String [1];
									siteGroup[0] = "L" + duInfo.duName.substring(1, 9);		// Per Ada, base site name length is consistently the same (not including ending 2/3/4 cases). 

									// #TC_216
									// [eshinai: 10/14/2019] Make appropriate adjustments for 4Sec the reconfig scenario.
									// NGS Needed only for 1st node (the one having 4 cells in kget and 3 in the RND).
									if((duInfo.kgetCellFddIds.size() == 4) && (duInfo.rndCellFddIds.size() == 3)) {
										// first node
										generateNGSfor5GFirstNodeScripts(duInfo, ngsDir + File.separator + duInfo.duName + "_NGS_3Sec_BB6630.mos", "DOS");
									}
									else if ((duInfo.kgetCellFddIds.size() == 0) && (duInfo.rndCellFddIds.size() == 1)) {
										// 2nd node
										// no need of NGS script for this case.
									}
									else {
										// generate regular NGS scripts otherwise.
										generate5GNR600NodeGroupSyncMemberScriptForNGS(duInfo, siteGroup[0], ngsDir + File.separator + duInfo.duName + "_NR_NGS.mos", "DOS");
										generateL600SplitLTENGSfor5GScriptBlock(siteGroup[0], ngsDir + File.separator + siteGroup[0] + "_NGS_3Sec_BB6630.mos", "DOS");		// '3Sec' in file name will be adjusted, if necessary, in method
									}
								}
							}
							
							// for carrier Add scopes, copy all _CarrierAdd_NR600.mos, eNB_ENDC_Creation.mos and LTE_PmFlexCounterFilter.mos files to a common bulk folder
							if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope() 
									&& !duInfo.tmoDUInfo.isTddCarrierAddScope)) {		// [12172021] GMO_TMO-206
								caBulkDir = FileUtil.createDirReturnStr(outputDir + File.separator + "BulkCarrierAdd");
								FileUtil.copyFilesToFolder(caDir, caBulkDir, ".*_CarrierAdd_NR600.mos$", false);
								if(!lteEndcCreationDir.isEmpty()) {
									FileUtil.copyFilesToFolder(lteEndcCreationDir, caBulkDir, ".*eNB_ENDC_Creation.*.mos$", false);
									FileUtil.copyFilesToFolder(lteEndcCreationDir, caBulkDir, ".*LTE_PmFlexCounterFilter.*.mos$", false);
								}
							}
							// [12172021] GMO_TMO-206
							if (!caDir.isEmpty())
								FileUtil.deleteDirIfEmpty(caDir);
							if (!ngsDir.isEmpty())
								FileUtil.deleteDirIfEmpty(ngsDir);
							if (!siteDir.isEmpty())
								FileUtil.deleteDirIfEmpty(siteDir);
							if (!caBulkDir.isEmpty())
								FileUtil.deleteDirIfEmpty(caBulkDir);
						} // if blnGenerateCarrierAddScripts
					} // duinfo is5G
				} // duInfo not null
			} // for each site in sites

			Logger.getGmoLogger().printHeaderTextWithTimeStamp("Finished generating 5G Carrier Add Scripts.");
		}
		catch (Exception e) {
			Logger.logger.error("generate5GCarrierAddScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating 5G Carrier Add scripts! " + e.getMessage());
		}
	}
	
	public void generateSmallCellScripts() {
		try {
			TMOMixedModeBasebandScripts tmoMixedModeBasebandScripts = new TMOMixedModeBasebandScripts(this);
			TMO_TDD_MixedModeBaseBandScripts tmoTDDMixedModeBaseBandScripts = new TMO_TDD_MixedModeBaseBandScripts(this);
			
			for (String site : sites) {
				SiteCellObj duInfo = tmoCCR.getDUToDUInfo().get(site);
				if (!duInfo.criticalErrors.isEmpty()) {
					for (String error : duInfo.criticalErrors) {
						Logger.logger.error(error);
						Logger.getGmoLogger().printError(error);
					}
					Logger.logger.error("Critical errors exist! Script generation stopped for " + site + ".");
					Logger.getGmoLogger().printErrorStandard(ErrorCategory.GMO_NOT_SUPPORTED, ErrorSubcategory.USE_CASE_NOT_FOUND,"Critical errors exist! Script generation stopped for " + site + ".");
					continue;
				}
				if(duInfo.tmoDUInfo.isExcaliburSmallCellSite) {
					String siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + String.join("_", sites));
					ParamPreservation pp = new ParamPreservation();
					pp.setSite(site);
					pp.setSoftwareLevel(duInfo.softwareLevel);
					pp.setBBU(duInfo.isBBU);
					pp.setInputFormat(duInfo.inputFormat);
					pp.setOutputFormat(duInfo.outputFormat);
					pp.setMarket(duInfo.getSiteObj().getMarket());
					pp.setTmoCCR(tmoCCR);
					pp.initializeGeneric();
					tmoMixedModeBasebandScripts.generateSmallCellAddScripts(duInfo, siteDir, pp);
					tmoTDDMixedModeBaseBandScripts.generateSmallCellAddScripts(duInfo, siteDir);
					
					// get gnbId using node name from RNDCIQ_GNBINFO
					String gnbId = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GNBINFO"), "gNB Name", site, "gNBId");
					if(gnbId != null && !gnbId.isEmpty()) {
			        //  get gnbId related records from RNDCIQ_GUTRANCELLINFO
					List<HashMap<String, String>> nr_gutranCellInfoMap = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GUTRANCELLINFO"), "gNBID", gnbId);
					if(nr_gutranCellInfoMap != null && !nr_gutranCellInfoMap.isEmpty()) {
	                       for(HashMap<String, String> gutranCellInfoRowData: nr_gutranCellInfoMap) {
	                    	   tmoMixedModeBasebandScripts.generateSmallCellENDCScripts(duInfo, siteDir, outputDir,gutranCellInfoRowData);
	                       }
						}
					}
					
					tmoMixedModeBasebandScripts.generateENDCScripts(duInfo, siteDir, outputDir);
					tmoMixedModeBasebandScripts.generateSyncReconfigurationScripts(duInfo, siteDir);
					generateCustomUpdateScript(duInfo, siteDir);
					generateREGScript(duInfo, siteDir);

				}
			}
		}
		catch(Exception e) {
			Logger.logger.error("generateSmallCellScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating generateSmallCellScripts scripts! " + e.getMessage());
		}
	}
	
	
	/**
	 * Function to generate MixedModeBaseband scripts
	 * @throws Exception
	 */
	private void generateMixedModeBasebandScripts() throws Exception
	{
		try {
			TMOMixedModeBasebandScripts tmoMixedModeBasebandScripts = new TMOMixedModeBasebandScripts(this);
			TMO_TDD_MixedModeBaseBandScripts tmoTddMmbbScripts = new TMO_TDD_MixedModeBaseBandScripts(this);
			boolean blnNRNodePresent = false;
			boolean isMNodePresent = false;
			Map<String, SiteCellObj> duToDUInfo = tmoCCR.getDUToDUInfo();
			SiteCellObj siteInfo = new SiteCellObj();
			for(String site: sites) {
				if (duToDUInfo.containsKey(site)) {
					siteInfo = duToDUInfo.get(site);
				}
				if(!siteInfo.isNRNodeLive && siteInfo.is5G) {
					blnNRNodePresent = true;
					break;
				}
			}
			for(String site: sites) {
				if(site.startsWith("M")) {
					isMNodePresent = true;
					break;
				}
			}
			
			String siteDir = "";
			int count = 0;
			for (String site : sites) {
				SiteCellObj duInfo = tmoCCR.getDUToDUInfo().get(site);
				
				if(duInfo.tmoDUInfo.isSetUp1DReconfig) {
					continue;
				}
				
				if ((duInfo.tmoDUInfo.isMixedModeBasebandScope || duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope || 
					duInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope || duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope) 
					&& !duInfo.tmoDUInfo.isMidbandMixedModeBasebandScope && !duInfo.tmoDUInfo.isTDDMixedModeBaseBandScope) {
					count++;
					if(blnNRNodePresent && isMNodePresent) {
						siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + String.join("_", sites));
					}else {
						siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + String.join("_", sites));
					}
					// Initialize ParamPreservation object for MMBB SOW
					ParamPreservation pp = new ParamPreservation();
					pp.setSite(site);
					pp.setSoftwareLevel(duInfo.softwareLevel);
					pp.setBBU(duInfo.isBBU);
					pp.setInputFormat(duInfo.inputFormat);
					pp.setOutputFormat(duInfo.outputFormat);
					pp.setMarket(duInfo.getSiteObj().getMarket());
					pp.setTmoCCR(tmoCCR);
					pp.initializeGeneric();
					
					if(duInfo.tmoDUInfo.isMixedModeBasebandScope || duInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope || 
						duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope || duInfo.tmoDUInfo.isExcalibur4G5GFDD) {
						tmoMixedModeBasebandScripts.generateAddScripts(duInfo, siteDir, pp);
						tmoMixedModeBasebandScripts.generateDeleteScripts(duInfo, siteDir);
						if(duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope) {
							if(!duInfo.tmoDUInfo.isMidBandTddMMBBVariation) {
								tmoMixedModeBasebandScripts.generateSyncReconfigurationScripts(duInfo, siteDir);
							}
						}
						else if(!(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())){
							tmoMixedModeBasebandScripts.generateSyncReconfigurationScripts(duInfo, siteDir);
						}
						
						if(!(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
							if (duInfo.tmoDUInfo.isExcalibur4G5GFDD) {
								duInfo.tmoDUInfo.isMixedModeBasebandScope = true;
								String site2 ="";
								if(duInfo.duName.endsWith("2") || duInfo.duName.endsWith("4") )
								{
									site2 = duInfo.duName.substring(0,duInfo.duName.length() - 1) + "3";
								}
								SiteCellObj duInfo2 =tmoCCR.getDUToDUInfo().get(site2);
								
								if(duInfo2!=null && duInfo2.duName!=null && !duInfo2.duName.isEmpty()) {
									tmoMixedModeBasebandScripts.generateInterNodeRelationScript(duInfo, siteDir, pp);
								}
								
								else if(duInfo2==null) { //Excalibur_225 when m3 node does not exists; still call interDU script 
									tmoMixedModeBasebandScripts.generateInterNodeRelationScript(duInfo, siteDir, pp);
								}
							}
							else {
								tmoMixedModeBasebandScripts.generateInterNodeRelationScript(duInfo, siteDir, pp);
							}
						}
						tmoMixedModeBasebandScripts.generateLockUnlockScripts(duInfo, siteDir);
						tmoMixedModeBasebandScripts.generateRollbackDeleteScripts(duInfo, siteDir);		// [06302020]
						tmoMixedModeBasebandScripts.generateENDCScripts(duInfo, siteDir, outputDir);
						tmoMixedModeBasebandScripts.generateCarolinaMarketSpecificScripts(duInfo, siteDir);
						if (duInfo.tmoDUInfo.isExcalibur4G5GFDD) {
							try {
								if(generateExcalibur) {
									String site3 = duInfo.duName.substring(1,duInfo.duName.length() - 1);
									SiteCellObj duInfo3 =tmoCCR.getDUToDUInfo().get(site3);
									if(duInfo3.has2GAnd3GSites) {
										tmoMixedModeBasebandScripts.generateLTENGSScriptBlock(duInfo, siteDir);
									}
								}
								else {
									tmoMixedModeBasebandScripts.generateLTENGSScriptBlock(duInfo, siteDir);
								}
							}
							catch(Exception e) {
								
							}
							generateCustomUpdateScript(duInfo, siteDir);
							if(duInfo.subNetwork.equals("Atlanta") || duInfo.subNetwork.equals("Miami") || duInfo.subNetwork.equals("Tampa") || duInfo.subNetwork.equals("Orlando") || duInfo.subNetwork.equals("Jacksonville")) {
							generateFDDRETScript(duInfo,siteDir);
							}
							generateREGScript(duInfo, siteDir);
						}

					}
					else if(duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope) {
						tmoMixedModeBasebandScripts.generateAddScripts(duInfo, siteDir, pp);
						tmoMixedModeBasebandScripts.generateDeleteScripts(duInfo, siteDir);
						tmoMixedModeBasebandScripts.generateInterNodeRelationScript(duInfo, siteDir, pp);
						tmoMixedModeBasebandScripts.generateLockUnlockScripts(duInfo, siteDir);
						tmoMixedModeBasebandScripts.generateRollbackDeleteScripts(duInfo, siteDir);
						tmoMixedModeBasebandScripts.generateCarolinaMarketSpecificScripts(duInfo, siteDir);
					}
					boolean isNbIotCellType3CellsPresent = false;
					if(duInfo.tmoDUInfo.duToDeltaAddNbIoTCells != null && duInfo.tmoDUInfo.duToDeltaAddNbIoTCells.size()>0) {
						List<String> nbIotCellType3Cells = duInfo.newCellToCellInfo.entrySet().stream().filter(entry -> !entry.getKey().isEmpty() && entry.getValue() != null && entry.getValue().tmoCellInfo.isNbIoTCell && entry.getValue().tmoCellInfo.nbIotCellType.contentEquals("3")).map(entry -> entry.getValue().cellName).collect(Collectors.toList());
						isNbIotCellType3CellsPresent = (nbIotCellType3Cells != null && nbIotCellType3Cells.size() > 0) ? true : isNbIotCellType3CellsPresent;
					}
					if(isNbIotCellType3CellsPresent)
						tmoMixedModeBasebandScripts.generateAllMarketNbIotScripts(duInfo, siteDir);	// [03242021] TC_394
					if(!duInfo.tmoDUInfo.isExcalibur4G5GFDD)
						tmoMixedModeBasebandScripts.generateEcBusDeleteScript(duInfo, siteDir); // [06112021-ezrxxsu] ACES
					
					if(!hasExcalibur4G5G && !hasExcaliburSmallCells && !has2GAnd3GSites) {
						if(duInfo.tmoDUInfo.isLegacyNodeNewSite && count == sites.size()) {
							tmoTddMmbbScripts.generateSCUScripts(inputDir, outputDir, this);
						}
					}
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateMixedModeBasebandScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating MixedModeBaseband scripts! " + e.getMessage());
		}
	}
	
	private void generateREGScript(SiteCellObj duInfo, String OutputDir) {
		// TODO Auto-generated method stub
		try {
			String OutputStr=OutputDir + File.separator + "01_" + duInfo.duName + File.separator + duInfo.duName + "_REG_LTE_NR_RevA.mos";

			RemoteTemplate.getXLSFileFromServer("templates/lte/sector_add/tmobile/multidusectoradd/reg/" + "REG_LTE_NR_RevA.mos", OutputStr, false);
		}
		catch(Exception e) {
			Logger.logger.error("Error retrieving REG_LTE_NR_RevA");
			Logger.getGmoLogger().printError("Error retrieving REG_LTE_NR_RevA");
		}
		
	}

	private void generateFDDRETScript(SiteCellObj duInfo, String OutputDir) {
		StringBuilder sb = new StringBuilder();
//		System.out.println("M node:" + duInfo.duName);
		ArrayList<HashMap<String, String>> cascadedRetDevices = CSVUtils
				.readDataRowArrayFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_RETDEVICES"), "eNodeB Name", duInfo.duName);

		String antUnitgrp = ""; 

		if (!(cascadedRetDevices.get(0).get("antenna model #1").equals("Andrew - HBXX-3319DS-A2M (Quad)")
				|| cascadedRetDevices.get(0).get("antenna model #1").equals("Commscope - FFHH-65A-R3 (Octo)")
				|| cascadedRetDevices.get(0).get("antenna model #1").equals("Commscope - FFV4-65C-R3-V1 (DoDeca)")
				|| cascadedRetDevices.get(0).get("antenna model #1").equals("Commscope - FFHH-65C-R3 (Octo)")
				|| cascadedRetDevices.get(0).get("antenna model #1").equals("Commscope - FFV4-65C-R6 (DoDeca)")
				|| cascadedRetDevices.get(0).get("antenna model #1").equals("Commscope - FFVV-65C-R3-V1 (Octo)")
				|| cascadedRetDevices.get(0).get("antenna model #1").equals("RFS - APXVAA4L24_43-U-NA20 (DoDeca)")
				|| cascadedRetDevices.get(0).get("antenna model #1").equals("Commscope - FFVV-65B-R3-V1 (Octo)")
				|| cascadedRetDevices.get(0).get("antenna model #1").equals("Commscope - FFHH-65B-R3 (Octo)"))) {
			Logger.logger.warn("Unknown Antenna model " + cascadedRetDevices.get(0).get("antenna model #1")
					+ ", Engg Action- Pls check the inputs and update Script as needed. ");
			Logger.getGmoLogger().printWarning(" Unknown Antenna model " + cascadedRetDevices.get(0).get("antenna model #1")
							+ ", Engg Action- Pls check the inputs and update Script as needed.");
		}
		if (cascadedRetDevices != null && !cascadedRetDevices.isEmpty() && cascadedRetDevices.get(0) != null
				&& !cascadedRetDevices.get(0).isEmpty()) {
			if (cascadedRetDevices.get(0).get("iuantDeviceType") != null
					&& !cascadedRetDevices.get(0).get("iuantDeviceType").isEmpty()
					&& cascadedRetDevices.get(0).get("iuantDeviceType").equals("1")) {

				sb.append("confb+" + eol + "gs+" + eol);
				List<String> retList = new LinkedList<>();
				String sectorNumber = null;

				for (Map<String, String> map : cascadedRetDevices) {
					String cellName = map.get("EutranCellFDDId");
					HashMap<String, String> cellLevelMapForeUtran = CSVUtils.readDataRowFromCSVFile(
							CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "EutranCellFDDId", cellName);
					String radioType = cellLevelMapForeUtran.get("Radio Type");
					sectorNumber = cellName.substring(cellName.length() - 2, cellName.length() - 1);
					antUnitgrp = getAntenaUnitGroup(radioType, sectorNumber);
					retList = new LinkedList<>();
					for (int i = 1; i <= 6; i++) {
						String retLabel = map.get("Ret User Label RET#" + i);
						if (retLabel != null & !retLabel.isEmpty()) {
							retList.add(retLabel);
						}
					}
					for (int j = 1; j <= retList.size(); j++) {
						sb.append("pr AntennaUnitGroup=" + antUnitgrp + ",AntennaUnit=1,AntennaSubunit=" + j)
								.append(eol);
						sb.append("if $nr_of_mos = 0").append(eol);
						sb.append("crn AntennaUnitGroup=" + antUnitgrp + ",AntennaUnit=1,AntennaSubunit=" + j)
								.append(eol);
						sb.append("end").append(eol);
						sb.append("fi").append(eol);
					}
				}
				String index = "";
				for (Map<String, String> map : cascadedRetDevices) {
					if (map.get("EutranCellFDDId")
							.substring(map.get("EutranCellFDDId").length() - 2, map.get("EutranCellFDDId").length() - 1)
							.equals("1")) {
						index = "1";
						sb.append("# Alpha # " + eol + eol);
					} else if (map.get("EutranCellFDDId")
							.substring(map.get("EutranCellFDDId").length() - 2, map.get("EutranCellFDDId").length() - 1)
							.equals("2")) {
						index = "2";
						sb.append("# Beta # " + eol + eol);
					} else if (map.get("EutranCellFDDId")
							.substring(map.get("EutranCellFDDId").length() - 2, map.get("EutranCellFDDId").length() - 1)
							.equals("3")) {
						index = "3";
						sb.append("# Gamma # " + eol + eol);
					} else if (map.get("EutranCellFDDId")
							.substring(map.get("EutranCellFDDId").length() - 2, map.get("EutranCellFDDId").length() - 1)
							.equals("4")) {
						index = "4";
						sb.append("# Alpha # " + eol + eol);
					} else if (map.get("EutranCellFDDId")
							.substring(map.get("EutranCellFDDId").length() - 2, map.get("EutranCellFDDId").length() - 1)
							.equals("5")) {
						index = "5";
						sb.append("# Beta # " + eol + eol);
					} else if (map.get("EutranCellFDDId")
							.substring(map.get("EutranCellFDDId").length() - 2, map.get("EutranCellFDDId").length() - 1)
							.equals("6")) {
						index = "6";
						sb.append("# Gamma # " + eol + eol);
					}

					String iuantDeviceType = map.get("iuantDeviceType");
					String cellName = map.get("EutranCellFDDId");
					HashMap<String, String> cellLevelMapForeUtran = CSVUtils.readDataRowFromCSVFile(
							CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "EutranCellFDDId", cellName);
					String radioType = cellLevelMapForeUtran.get("Radio Type");
					sectorNumber = cellName.substring(cellName.length() - 2, cellName.length() - 1);
					antUnitgrp = getAntenaUnitGroup(radioType, sectorNumber);
					String fieldReplaceableUnit = getFieldReplaceableType(cellName, radioType, sectorNumber);
					retList = new LinkedList<>();
					for (int i = 1; i <= 6; i++) {
						String retLabel = map.get("Ret User Label RET#" + i);
						if (retLabel != null & !retLabel.isEmpty()) {
							retList.add(retLabel);
						}
					}
//			sb.append("" + Eutrancell + eol);
					int k = 1;
					for (int j = 1; j <= retList.size(); j++) {
						k = j >= 2 ? j + 1 : j;
						sb.append("pr Equipment=1,AntennaUnitGroup=" + antUnitgrp + ",AntennaNearUnit=" + k)
								.append(eol);
						sb.append("if $nr_of_mos = 0").append(eol);
						sb.append("crn Equipment=1,AntennaUnitGroup=" + antUnitgrp + ",AntennaNearUnit=" + k)
								.append(eol);
						sb.append("iuantDeviceType " + iuantDeviceType).append(eol);
						
						sb.append("rfPortRef FieldReplaceableUnit=" + fieldReplaceableUnit + ",RfPort=R")
									.append(eol);
						sb.append("uniqueId " + map.get("uniqueHwId RET#" + j)).append(eol);
						sb.append("end").append(eol);
						sb.append("fi").append(eol);
						sb.append("").append(eol);

						sb.append("pr Equipment=1,AntennaUnitGroup=" + antUnitgrp + ",AntennaNearUnit=" + k
								+ ",RetSubUnit=1").append(eol);
						sb.append("if $nr_of_mos = 0").append(eol);
						sb.append("crn Equipment=1,AntennaUnitGroup=" + antUnitgrp + ",AntennaNearUnit=" + k
								+ ",RetSubUnit=1").append(eol);
						sb.append("electricalAntennaTilt " + map.get("electricalTilt RET#" + j)).append(eol);
						sb.append("userlabel " + retList.get(j - 1)).append(eol);
						sb.append("end").append(eol);
						sb.append("fi").append(eol);
						sb.append("").append(eol);

					}
				}
				sb.append("").append(eol);
				sb.append("").append(eol);
				for (Map<String, String> map : cascadedRetDevices) {
					String cellName = map.get("EutranCellFDDId");
					HashMap<String, String> cellLevelMapForeUtran = CSVUtils.readDataRowFromCSVFile(
							CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "EutranCellFDDId", cellName);
					String radioType = cellLevelMapForeUtran.get("Radio Type");
					sectorNumber = cellName.substring(cellName.length() - 2, cellName.length() - 1);
					antUnitgrp = getAntenaUnitGroup(radioType, sectorNumber);
					retList = new LinkedList<>();
					for (int i = 1; i <= 6; i++) {
						String retLabel = map.get("Ret User Label RET#" + i);
						if (retLabel != null & !retLabel.isEmpty()) {
							retList.add(retLabel);
						}
					}
					int k = 1;
					for (int j = 1; j <= retList.size(); j++) {
						k = j >= 2 ? j + 1 : j;
						sb.append("lset Equipment=1,AntennaUnitGroup=" + antUnitgrp + ",AntennaUnit=1,AntennaSubunit=" + j + "$ retSubunitRef Equipment=1,AntennaUnitGroup=" + antUnitgrp + ",AntennaNearUnit=" + k + ",RetSubUnit=1").append(eol);
					}
				}
				sb.append("").append(eol);
				sb.append("get ant rfport").append(eol);
				sb.append("get . Uniqueid").append(eol);
				sb.append("get . Iuantd").append(eol);
				sb.append("st rfport ").append(eol);
				sb.append("get . Retsubunitref ").append(eol);
				sb.append("st nearunit ").append(eol);
				sb.append("hget rets model|operational|adminis|tilt|sector|base|userlabel").append(eol);
				sb.append("").append(eol);
				sb.append("gs-").append(eol);
				sb.append("confb-").append(eol);

				String OutputStr = OutputDir + File.separator + "01_" + duInfo.duName + File.separator + duInfo.duName
						+ "_RET_FDD_Excalibur.mos";
				FileUtil.writeToFile(sb, OutputStr);
			} else {
				Logger.logger.error(" GMO partially not supported - Iuantdevicetype not Supported- Unknown value "
						+ cascadedRetDevices.get(0).get("iuantDeviceType")
						+ ", Engg Action- Pls check the inputs and update Script as needed.");
				Logger.getGmoLogger()
						.printError("GMO partially not supported - Iuantdevicetype not Supported- Unknown value "
								+ cascadedRetDevices.get(0).get("iuantDeviceType")
								+ ", Engg Action- Pls check the inputs and update Script as needed.");
			}
		} else {
			Logger.logger.error("Tab Cascaded RET Devices is completly Blank");
			Logger.getGmoLogger().printError("Tab Cascaded RET Devices is completly Blank");
		}

	}
	
	private String getAntenaUnitGroup(String radioType,String sector) {
		String antenaUnitGroup = "";
		if(radioType.contains("4424")) {
			//19-XX
			antenaUnitGroup ="19-0" + sector;
		}else if(radioType.contains("4415")) {
			//21-xx
			antenaUnitGroup ="21-0" + sector;
		}else if(radioType.contains("4449") || radioType.contains("4480")) {
			//6-XX
			antenaUnitGroup ="6-0" + sector;
		}else if(radioType.contains("4460")) {
			//AWPC-XX
			antenaUnitGroup ="AWPC-0" + sector;

		}
		return antenaUnitGroup;
	}
	
	private String getFieldReplaceableType(String cellName,String radioType,String sector) {
		if(radioType.contains("4415") || radioType.contains("4449") || radioType.contains("4480")) {
			return getAntenaUnitGroup(radioType, sector);
		} else if(radioType.contains("4460") || radioType.contains("4424")){
			if(cellName.endsWith("1")) {
				return getAntenaUnitGroup(radioType, sector) + "-01";
			}else if(cellName.endsWith("2")) {
				return getAntenaUnitGroup(radioType, sector) + "-02";
			}
		}
		return null;
	}
	

	/**
	 * @param duInfo
	 * @param sb
	 */
	// [10012021] GMO_TMO-177
	protected StringBuilder addMinTiltMaxTiltParam(String softwareLevel, String minTilt, String maxTilt)
	{
		StringBuilder sb = new StringBuilder();
		if (CommonUtil.checkSoftwareGreaterOrEqual(softwareLevel, "21.Q3")) {
			sb.append("minTilt " + minTilt + eol);
			sb.append("maxTilt " + maxTilt + eol);
		}
		return sb;
	}

	/**
	 * Function to generate Excalibur custom Update Script
	 */
	public StringBuilder generateCustomUpdateScript(SiteCellObj duInfo, String OutputDir) {
		StringBuilder sb = new StringBuilder();
		
		sb.append("gs+" + eol
				+ "confb+" + eol
				+ "lt all" + eol
				+ eol
				+ " " + eol);
		ArrayList<String> enbInfo = CSVUtils.readDataArrayFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"),"eNodeB Name",duInfo.duName,"eNBId",false);
		if(enbInfo!=null && !enbInfo.isEmpty()) {
			ArrayList<String> umtsLteCells = CSVUtils.readDataArrayFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM"),"eNBId",enbInfo.get(0),"EutranCellFDDId",false);
			String crsGain;
			boolean pdschType = false;
			int count = 0;
			int CountTdd = 0;
			for(String cell:umtsLteCells) {
				if(cell.startsWith("B")||cell.startsWith("L")||cell.startsWith("D")||cell.startsWith("E")||cell.startsWith("F") ) {
					crsGain = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "EutranCellFDDId",cell ,"crsGain");
					if(crsGain!=null && !crsGain.isEmpty()) {
						sb.append("set EUtranCellFDD=" + cell + "$ crsGain " + crsGain + eol);
					}
					else {
						sb.append("//set EUtranCellFDD=" + cell + "$ crsGain " + crsGain + eol);
						Logger.logger.error(cell + " crsGain Value is missing/Empty on the RNDCIQ");
						Logger.getGmoLogger().printError(cell + " crsGain Value is missing/Empty on the RNDCIQ");
					}
					count++;
					
				}
				else {
					CountTdd++;
					crsGain = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "EutranCellFDDId",cell ,"crsGain");
					if(crsGain!=null && !crsGain.isEmpty() ) {
						sb.append("set EUtranCellTDD=" + cell + "$ crsGain " + crsGain + eol);
						
					}
					else {
						sb.append("//set EUtranCellTDD=" + cell + "$ crsGain " + crsGain + eol);
						Logger.logger.error(cell + " crsGain Value is missing/Empty on the RNDCIQ");
						Logger.getGmoLogger().printError(cell + " crsGain Value is missing/Empty on the RNDCIQ");
					}
				}

			}
			try {
				if(count>1 && duInfo.tmoDUInfo.isExcalibur4G5GFDD) {
					sb.append("set ENodeBFunction=1,CarrierAggregationFunction=1$ endcCaPolicy 1 " + eol);
				}else if(CountTdd>=1 && duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
					sb.append("set ENodeBFunction=1,CarrierAggregationFunction=1$ endcCaPolicy 0 " + eol);
				}
				String transmissionMode="";
				for(String cell:umtsLteCells) {
					transmissionMode = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "EutranCellFDDId",cell ,"Transmission Mode");
					if(cell.startsWith("B")||cell.startsWith("L")||cell.startsWith("D")||cell.startsWith("E")||cell.startsWith("F") ) {
						crsGain = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "EutranCellFDDId",cell ,"crsGain");
						if(crsGain!=null && !crsGain.isEmpty() && crsGain.equals("0")) {
							sb.append("set EUtranCellFDD=" + cell + "$ pdschTypeBGain 0 " + eol);
						}
						if(transmissionMode!=null && !transmissionMode.isEmpty()&& transmissionMode.equals("CLSM")) {
							sb.append("set EUtranCellFDD=" + cell + "$ transmissionMode 4 " + eol);
						}
					}
					else {
						crsGain = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "EutranCellFDDId",cell ,"crsGain");
						if(crsGain!=null && !crsGain.isEmpty() && crsGain.equals("0") ) {	
							sb.append("set EUtranCellTDD=" + cell + "$ pdschTypeBGain 0 " + eol);
						}
					}
				}
				
				sb.append(eol);
				// set adjustCrsPowerEnhEnabled true where crsGain >300
				if(hasExcalibur4G5G || hasExcaliburSmallCells) {
					boolean isAdjustCrsPowerEnhEnabled = false;
				for(String cell:umtsLteCells) {

					if(cell.startsWith("B")||cell.startsWith("L")||cell.startsWith("D")||cell.startsWith("E")||cell.startsWith("F") ) {
						crsGain = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "EutranCellFDDId",cell ,"crsGain");
						if(crsGain!=null && !crsGain.isEmpty()) {
							if(duInfo.tmoDUInfo.isExcalibur4G5GFDD && Integer.valueOf(crsGain) > 300) {
								if(!isAdjustCrsPowerEnhEnabled) {
									sb.append("####adjustCrsPowerEnhEnabled true|crsGain >300 in CIQ##" + eol);
									isAdjustCrsPowerEnhEnabled = true;
									}
								
								sb.append("set EUtranCellFDD="+ cell + "$  adjustCrsPowerEnhEnabled true" + eol);
							}
						}
						
					}
					else {
						crsGain = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_EUTRANPARAM"), "EutranCellFDDId",cell ,"crsGain");
						if(crsGain!=null && !crsGain.isEmpty() ) {
							if(duInfo.tmoDUInfo.isExcalibur4G5GTDD && Integer.valueOf(crsGain) > 300) {
								
								if(!isAdjustCrsPowerEnhEnabled) {
									sb.append("####adjustCrsPowerEnhEnabled true|crsGain >300 in CIQ##" + eol);
									isAdjustCrsPowerEnhEnabled = true;
									}
								sb.append("set EUtranCellTDD="+ cell + "$  adjustCrsPowerEnhEnabled true" + eol);
							}
						}
						
					}

				}
			}
				

				ArrayList<String> gnbInfo = CSVUtils.readDataArrayFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GNBINFO"),"gNB Name",duInfo.duName,"gNBId",false);
				sb.append("\n###NR SETTING###" + eol);
				ArrayList<String> gUtranCells = CSVUtils.readDataArrayFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GUTRANCELLINFO"),"gNBID",gnbInfo.get(0),"gUtranCell",false);
				for(String cell: gUtranCells) {
					
					String cellRange = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GUTRANCELLINFO"),"gUtranCell", cell, "cellRange"); 
					if(cellRange.equals(null) || cellRange.equals("")) {
						Logger.logger.warn("cellRange not found for " + cell);
						Logger.getGmoLogger().printTextWithTimeStamp("cellRange not found for " + cell);

						sb.append("//set NRCellDU=" + cell + " cellRange" + eol);
					}
					else {
						sb.append("set NRCellDU=" + cell + " cellRange " + cellRange + eol);
					}
				}
				sb.append(eol);
			if(hasExcalibur4G5G || hasExcaliburSmallCells){
				boolean isRachPreambleFormat = false;
				for(String cell: gUtranCells) {
					
					String cellRange = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GUTRANCELLINFO"),"gUtranCell", cell, "cellRange"); 
					if(cellRange !=null) {
						if(!isRachPreambleFormat ) {
						sb.append("#####rachPreambleFormat 0 cellRange <= 15000 | rachPreambleFormat 2 cellRange is > 15000 ####" + eol);
						isRachPreambleFormat = true;
						}
						if(Integer.valueOf(cellRange) <=15000) {
							sb.append("set NRCellDU=" + cell + " rachPreambleFormat 0" + eol);
					  }	else if(Integer.valueOf(cellRange)>15000) {
						  sb.append("set NRCellDU=" + cell + " rachPreambleFormat 2" + eol);
					  }
					}
				}
			  }
			}
			catch(Exception e ) {
				
			}
			
			sb.append(eol);
			sb.append(		
					"  " + eol
					+ "gs-" + eol
					+ "confb-");
		}
		
		String OutputStr=OutputDir + File.separator + "01_" + duInfo.duName + File.separator + duInfo.duName + "_custom_update.mos";
		FileUtil.writeToFile(sb, OutputStr);
		
		return sb;
	}
	
	
	/**
	 * Function to generate MidbandMixedModeBaseband scripts
	 * @throws Exception
	 */
	private void generateMidbandMixedModeBasebandScripts() throws Exception
	{
		try {
			Map<String, SiteCellObj> duToDUInfo = tmoCCR.getDUToDUInfo();
			SiteCellObj duInfo = new SiteCellObj();
			for(String site: sites) {
				if (duToDUInfo.containsKey(site)) {
					duInfo = duToDUInfo.get(site);
				}
				if(duInfo.tmoDUInfo.isMidbandMixedModeBasebandScope) {
					int duCount = sites.size();
					Set<String> liveN66Cells = duInfo.newCellToCellInfo.entrySet().stream().filter(entry -> entry.getValue().isLiveCell && entry.getKey().matches("(I|J).*")).map(entry -> entry.getKey()).collect(Collectors.toSet());
					boolean triggerScriptsForFDDMMMBBLegacyNode = duInfo.nodeBandType.equals("N66") && liveN66Cells.size() == 0 && duInfo.tmoDUInfo.isMidBandFddMMBBVariation;
					boolean triggerScriptsForFddMidBandN25LegacyNode = isTestServer && duInfo.nodeBandType.equals("N25") && duInfo.tmoDUInfo.isMidBandFddMMBBVariation;			// [04012022] GMO_TMO-274, N25 MMBB from live LTE with AWS (B4-L cells), PCS (B2-B cells)
					boolean triggerENDCScript = false;
					boolean triggerGUtranCellRelationScript = false;
					boolean triggerGUtranFreqRelationsScript = triggerScriptsForFDDMMMBBLegacyNode || triggerScriptsForFddMidBandN25LegacyNode;
					boolean triggerBaselineScripts = triggerScriptsForFDDMMMBBLegacyNode || triggerScriptsForFddMidBandN25LegacyNode;
					duInfo.tmoDUInfo.triggerN66N25BaselinewithAMFSAScript = triggerScriptsForFDDMMMBBLegacyNode;
					boolean triggerTrafficAddScripts = triggerScriptsForFDDMMMBBLegacyNode || triggerScriptsForFddMidBandN25LegacyNode;
					boolean triggerIntraFreqScripts = triggerScriptsForFDDMMMBBLegacyNode || triggerScriptsForFddMidBandN25LegacyNode;
					boolean triggerNr41EranScript = duInfo.nodeBandType.equals("N41") && (!isTestServer || (isTestServer && !duInfo.tmoDUInfo.isN25MidBandScope));			// [04082022] GMO_TMO-274 Updated
					boolean triggerNRtoNRScript = duInfo.tmoDUInfo.triggerNR2NRRelationScript && (!duInfo.nodeBandType.equals("N41") || !triggerNr41EranScript);			// [04082022] GMO_TMO-274 Updated
					boolean triggerNRtoLTERelationScript =  tmoDC.triggerGenericNRToLTERelationUpdated(duInfo);
					String duName = duInfo.tmoDUInfo.triggerFingerprintAligmentScripts ? duInfo.duName : duInfo.existingDuName;
					duName = triggerScriptsForFddMidBandN25LegacyNode ? duInfo.duName : duName;					// [04012022] GMO_TMO-274 Existing LTE node becoming MMBB node
					boolean triggerGutranFreqRelationScript = isTestServer && duInfo.tmoDUInfo.isN25MidBandScope && !duInfo.tmoDUInfo.isMidBandFddMMBBVariation ? true : false;	// [04082022] GMO_TMO-274
			
					String siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + String.join("_", sites) + File.separator + duName);
					TMOMidBandMixedModeBasebandScripts tmoMidBandMixedModeBasebandScripts = new TMOMidBandMixedModeBasebandScripts(this);
					if(triggerTrafficAddScripts)
						tmoMidBandMixedModeBasebandScripts.generateMidbandMMBBTrafficAddScript(duInfo, siteDir, duName);
					if(triggerGUtranCellRelationScript)
						tmoMidBandMixedModeBasebandScripts.generateMidbandMMBBGUtranCellRelationScript(duInfo, siteDir, duName);
					if(triggerENDCScript)
						tmoMidBandMixedModeBasebandScripts.generateMidbandMMBBEndcScript(duInfo, siteDir, duCount, duName);
					if(triggerIntraFreqScripts)
						tmoMidBandMixedModeBasebandScripts.generateMidbandMMBBIntraFreqScript(duInfo, siteDir, duCount, duName);
					if(triggerGUtranFreqRelationsScript)
						tmoMidBandMixedModeBasebandScripts.generateMidbandMMBBStandaloneGUtranFreqRelationsScript(duInfo, siteDir, duCount, duName);
					if(triggerBaselineScripts) {
						BaselineUtil baseline = new BaselineUtil();
						baseline.generate5GNsbBaselineScripts(duInfo, siteDir);
						if (isTestServer && triggerScriptsForFddMidBandN25LegacyNode && !duInfo.existingDuName.startsWith("L")) {		// [04012022] GMO_TMO-274. when adding J cells on existing NR node with N71 (K cell) already live
							baseline.generateCellBased5GCarrierAddBaseline(duInfo, "5G", "Carrier_add", baseline.baseline5gCarrierAddMap(), siteDir);
						}
					}
					if(triggerNRtoNRScript)
						tmoMidBandMixedModeBasebandScripts.generateMidbandMMBBNrToNrScript(duInfo, siteDir);
					if(triggerNr41EranScript)
						tmoMidBandMixedModeBasebandScripts.generateMidbandMMBBNr41EranScript(duInfo, siteDir);
					if(triggerNRtoLTERelationScript)
						tmoMidBandMixedModeBasebandScripts.generateMidbandMMBBNrToLteScript(duInfo, siteDir, duName);
					if(duInfo.tmoDUInfo.triggerFingerprintAligmentScripts) {
						FingerprintAlignment fingerprintAlignment = new FingerprintAlignment(inputDir, siteDir, duInfo.duName, duToDUInfo);
						fingerprintAlignment.execute();
						tmoMidBandMixedModeBasebandScripts.generateMidbandMMBBENMDeleteScript(duInfo, siteDir, duName);

						if(isTestServer && duInfo.tmoDUInfo.isN25MidBandScope && duInfo.tmoDUInfo.isMidBandFddMMBBVariation) {		// [04072022] GMO_TMO-274
							String termPointUnlockScriptFile = siteDir + File.separator + duName + "_termpoint_unlock.mos";
							TmoG2ToG3PostProcess tmoG2G2 = new TmoG2ToG3PostProcess(duToDUInfo);
							tmoG2G2.generateTermPointUnlockScript(duInfo, termPointUnlockScriptFile);
						}
					}

					//GutranFreqRelation Script
					if(triggerGutranFreqRelationScript) {			// [04072022] GMO_TMO-274
						tmoMidBandMixedModeBasebandScripts.generateMidbandMmbbGUtranFreqRelationsScript(duInfo, siteDir, duName);
					}
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateMidbandMixedModeBasebandScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating MidbandMixedModeBaseband scripts! " + e.getMessage());
		}
	}
	
	/**
	 * Function to generate TDD MMBB Variation scripts
	 * @throws Exception
	 */
	private void generateTDDMixedModeBaseBandScripts() throws Exception
	{
		try {
			TMO_TDD_MixedModeBaseBandScripts tmoTDDMixedModeBaseBandScripts = new TMO_TDD_MixedModeBaseBandScripts(this);
			Map<String, SiteCellObj> duToDUInfo = tmoCCR.getDUToDUInfo();
			SiteCellObj duInfo = new SiteCellObj();
			for(String site: sites) {
				if (duToDUInfo.containsKey(site)) {
					duInfo = duToDUInfo.get(site);
				}
				if(duInfo != null) {
					if(duInfo.tmoDUInfo.isSetUp1DReconfig) {
						continue;
					}
					
					if (!duInfo.criticalErrors.isEmpty()) {
						for (String error : duInfo.criticalErrors) {
							Logger.logger.error(error);
							Logger.getGmoLogger().printError(error);
						}
						Logger.logger.error("Critical errors exist! Script generation stopped for " + site + ".");
						Logger.getGmoLogger().printErrorStandard(ErrorCategory.GMO_NOT_SUPPORTED, ErrorSubcategory.USE_CASE_NOT_FOUND,"Critical errors exist! Script generation stopped for " + site + ".");
						continue;
					}
					ParamPreservation pp = new ParamPreservation();
					pp.setSite(site);
					pp.setSoftwareLevel(duInfo.softwareLevel);
					pp.setBBU(duInfo.isBBU);
					pp.setInputFormat(duInfo.inputFormat);
					pp.setOutputFormat(duInfo.outputFormat);
					pp.setMarket(duInfo.getSiteObj().getMarket());
					pp.setTmoCCR(tmoCCR);
					pp.initializeGeneric();
					
					if(duInfo.tmoDUInfo.isTDDMixedModeBaseBandScope || duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope ||
						duInfo.tmoDUInfo.isMidBandTdd2CAddMixedModeBaseBandScope || duInfo.tmoDUInfo.isLiveLowBandAndTdd2CAddMixedModeBaseBandScope ||
						(duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope && duInfo.tmoDUInfo.isMidBandTddMMBBVariation)) {
						String siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + String.join("_", sites));
						tmoTDDMixedModeBaseBandScripts.generateAddScripts(duInfo, siteDir);
						if(duInfo.tmoDUInfo.isTDDMixedModeBaseBandScope || duInfo.tmoDUInfo.isMidBandTdd2CAddMixedModeBaseBandScope || 
							duInfo.tmoDUInfo.isLiveLowBandAndTdd2CAddMixedModeBaseBandScope) {
							tmoTDDMixedModeBaseBandScripts.generateInterNodeRelationScript(duInfo, siteDir, pp);
						}
						if(!duInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope) {
							tmoTDDMixedModeBaseBandScripts.generateENDCScripts(duInfo, siteDir);
							tmoTDDMixedModeBaseBandScripts.generateSyncReconfigurationScripts(duInfo, siteDir);
						}
						if(duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
							generateCustomUpdateScript(duInfo, siteDir);
							generateTDDRETScript(duInfo,siteDir);
							generateREGScript(duInfo, siteDir);
						}
					}
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateTDDMixedModeBaseBandScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating TDD MixedModeBaseband scripts! " + e.getMessage());
		}
	}
	
	private void generateMixedModeBaseBandScriptsForNewConfig() throws Exception
	{
		try {
			TMOMixedModeBasebandScripts tmoMmbbScripts = new TMOMixedModeBasebandScripts(this);
			TMO_TDD_MixedModeBaseBandScripts tmoTddMmbbScripts = new TMO_TDD_MixedModeBaseBandScripts(this);
			Map<String, SiteCellObj> duToDUInfo = tmoCCR.getDUToDUInfo();

			SiteCellObj duInfo = new SiteCellObj();
			int count = 0;
			for(String site: sites) {
				if (duToDUInfo.containsKey(site)) {
					duInfo = duToDUInfo.get(site);
				}
				
				if(duInfo != null && ((duInfo.isNewSite && (duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode() || duInfo.tmoDUInfo.getIsStandAloneMidBandMmbbNode())) || duInfo.tmoDUInfo.isSetUp1DReconfig)) {
					if (!duInfo.criticalErrors.isEmpty()) {
						for (String error : duInfo.criticalErrors) {
							Logger.logger.error(error);
							Logger.getGmoLogger().printError(error);
						}
						Logger.logger.error("Critical errors exist! Script generation stopped for " + site + ".");
						Logger.getGmoLogger().printError("Critical errors exist! Script generation stopped for " + site + ".");
						continue;
					}
					Collections.sort(duInfo.tmoDUInfo.duToDeltaAddCells);
					count++;
					String siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + String.join("_", sites));
					ParamPreservation pp = new ParamPreservation();
					pp.setSite(site);
					pp.setSoftwareLevel(duInfo.softwareLevel);
					pp.setBBU(duInfo.isBBU);
					pp.setInputFormat(duInfo.inputFormat);
					pp.setOutputFormat(duInfo.outputFormat);
					pp.setMarket(duInfo.getSiteObj().getMarket());
					pp.setTmoCCR(tmoCCR);
					pp.initializeGeneric();

					if(duInfo.duName.startsWith("M"))
						Logger.getGmoLogger().printStart("Generating scripts for " + duInfo.duName + " for configuration = [" + duInfo.designConfig + "]");
					else
						Logger.getGmoLogger().printStart("Generating scripts for " + duInfo.duName);
					if(duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode() || duInfo.tmoDUInfo.isLowBandSetUp1DReconfig) {
						List<String> removedCells = new ArrayList<>();
						SiteCellObj cellInfo = new SiteCellObj();
						if(duInfo.tmoDUInfo.duToDeltaAddCells != null && duInfo.tmoDUInfo.duToDeltaAddCells.size() > 0) {
							for(String currCellFddName: duInfo.tmoDUInfo.duToDeltaAddCells) {
								if(duInfo.newCellToCellInfo.containsKey(currCellFddName)) {
									cellInfo = duInfo.newCellToCellInfo.get(currCellFddName);
									if(cellInfo != null && (cellInfo.tmoCellInfo.bandCMCIQ == null || cellInfo.tmoCellInfo.bandCMCIQ.isEmpty())) {
										removedCells.add(currCellFddName);
									}
								}
							}
							
							duInfo.tmoDUInfo.duToDeltaAddCells.removeAll(removedCells);
						}
					}
					
					if(duInfo.tmoDUInfo.isLowBandSetUp1DReconfig) {
						TMO_CommonUtil.calculateTriggerForNbIotBaseline(duInfo);
						TMO_CommonUtil.initAdditionalPlmnData(duInfo);
						TMO_CommonUtil.collectUpgradePackageForLowBand(duInfo, duToDUInfo);
					}
					
					if(duInfo.tmoDUInfo.isLowBandSetUp1DReconfig || duInfo.tmoDUInfo.isStandAloneLowBandMmbbNode) {
						TMO_CommonUtil.calculateTriggerRetBlockForCells(duInfo);
					}
					tmoMmbbScripts.generateAddScripts(duInfo, siteDir, pp);//Add Scripts - LB MMBB
					
					tmoTddMmbbScripts.generateAddScripts(duInfo, siteDir);//Add Scripts - TDD MMBB
					if(sites.size() > 1) {
						boolean isExternalNodePresent = false;
						for(String node: sites) {
							String siteStr = duInfo.duName.replaceAll("^[A-Za-z]", "").replaceAll("[\\d]+$", "");
							if(!node.equals(duInfo.duName) && node.matches(".*" + siteStr + ".*") && !node.startsWith("N")) {
								isExternalNodePresent = true;
								break;
							}
						}
						if(isExternalNodePresent)
							tmoMmbbScripts.generateInterNodeRelationScript(duInfo, siteDir, pp);//InterDU Scripts - LB/TDD MMBB
						
						boolean triggerPTPScript = true;
						if(duInfo.tmoDUInfo.isLowBandSetUp1DReconfig) {
							triggerPTPScript = (!isExternalNodePresent && duInfo.tmoDUInfo.isSASRouterType) ? false : triggerPTPScript;
						}
						if(triggerPTPScript)					
							tmoTddMmbbScripts.generateSyncReconfigurationScripts(duInfo, siteDir);//PTP Scripts - LB/TDD MMBB
					}
					
					tmoMmbbScripts.generateENDCScripts(duInfo, siteDir, outputDir);//ENDC Scripts - LB/TDD MMBB
					
					if(duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode() || duInfo.tmoDUInfo.isLowBandSetUp1DReconfig) {
						if(duInfo.tmoDUInfo.duToLteNGSCells !=null && duInfo.tmoDUInfo.duToLteNGSCells.size() > 0) {
							tmoTddMmbbScripts.generateLTENGSScript(duInfo, siteDir);//LTE NGS Script - LB MMBB
						}
						tmoTddMmbbScripts.generateRilinkBlock(duInfo, siteDir);// Rilink Block - LB MMBB
						if(duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode() || duInfo.tmoDUInfo.isLowBandSetUp1DReconfig) {
							tmoMmbbScripts.generateNbIotAddScriptForNewConfig(duInfo, siteDir);//NbIot Add Scripts - LB MMBB
							if(duInfo.tmoDUInfo.triggerECSupportSystemControlScript)
								tmoMmbbScripts.generateSupportSystemControlScript(duInfo, siteDir); //EC SSC Script
						}
						tmoMmbbScripts.generateL700RadioNameUpdateScript(duInfo, siteDir);
						
						if(duInfo.tmoDUInfo.isLowBandSetUp1DReconfig) {
							tmoMmbbScripts.generateEUtranCellFddDeleteScript(duInfo, siteDir);
						}
					}

					//G2-G3 Migration Scripts
					if(duInfo.tmoDUInfo.isLowBandSetUp1DReconfig && (duInfo.tmoDUInfo.triggerG2G3MigrationForSetUp1DReconfig || duInfo.tmoDUInfo.triggerG3FingerPrintChangeForSetUp1DReconfig)) {
						String migrationInputDir = TMO_CommonUtil.initG2G3MigrationZipFiles(inputDir);
						String migrationOutputDir = FileUtil.createDirReturnStr(outputDir + File.separator + "03_G2_G3_Migration_Script");
						TmoG2ToG3PostProcess tmoG2G3 = new TmoG2ToG3PostProcess(migrationInputDir, migrationOutputDir, duInfo.existingDuName, duToDUInfo);
						tmoG2G3.setNSBOption(true);
						Map<String, String> map = new HashMap<>();
						map.put(duInfo.existingDuName, duInfo.duName);
						tmoG2G3.setExistingNodeToNewNodeNameMap(map);
						tmoG2G3.generatePostProcessScripts();
					}
					
					if(count == sites.size())
						tmoTddMmbbScripts.generateSCUScripts(inputDir, outputDir, this);
					Logger.getGmoLogger().printEnd("Generating scripts for " + duInfo.duName);
				}
			}
			
			String migrationFilePath = inputDir + File.separator + "G2_G3_Input";
			if(new File(migrationFilePath).exists()) {
				CleanUtil.deleteDirectory(migrationFilePath);
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateMixedModeBaseBandScriptsForNewConfig exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating MMBB scripts! " + e.getMessage());
		}
	}
	
	// [12032021] TMO_GMO-206 for TDD NR41 2C add to MMBB or non-MMBB node
	private void generatedTddCarrierAddScripts() throws Exception
	{
		try {
			TMOMixedModeBasebandScripts tmoMmbbScripts = new TMOMixedModeBasebandScripts(this);
			TMO_TDD_MixedModeBaseBandScripts tmoTddMmbbScripts = new TMO_TDD_MixedModeBaseBandScripts(this);
			Map<String, SiteCellObj> duToDUInfo = tmoCCR.getDUToDUInfo();
			
			SiteCellObj duInfo = new SiteCellObj();
			for(String site: sites) {
				if (duToDUInfo.containsKey(site)) {
					duInfo = duToDUInfo.get(site);
				}
				
				if(duInfo != null && !duInfo.isNewSite && duInfo.tmoDUInfo.isTddCarrierAddScope) {
					if (!duInfo.criticalErrors.isEmpty()) {
						for (String error : duInfo.criticalErrors) {
							Logger.logger.error(error);
							Logger.getGmoLogger().printError(error);
						}
						Logger.logger.error("Critical errors exist! Script generation stopped for " + site + ".");
						Logger.getGmoLogger().printError("Critical errors exist! Script generation stopped for " + site + ".");
						continue;
					}

					// Not sure if this is required, keep for now
					List<String> removedCells = new ArrayList<>();
					SiteCellObj cellInfo = new SiteCellObj();
					if(duInfo.tmoDUInfo.duToDeltaNR600AddCells != null && duInfo.tmoDUInfo.duToDeltaNR600AddCells.size() > 0) {
						for(String currCellFddName: duInfo.tmoDUInfo.duToDeltaAddCells) {
							if(duInfo.newCellToCellInfo.containsKey(currCellFddName)) {
								cellInfo = duInfo.newCellToCellInfo.get(currCellFddName);
								if(cellInfo != null && (cellInfo.tmoCellInfo.bandCMCIQ == null || cellInfo.tmoCellInfo.bandCMCIQ.isEmpty())) {
									removedCells.add(currCellFddName);
								}
							}
						}

						duInfo.tmoDUInfo.duToDeltaAddCells.removeAll(removedCells);
					}

					String siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + String.join("_", sites));
					tmoTddMmbbScripts.generateNrCarrierAddScripts(duInfo, siteDir); //Add Scripts - NR, TDD Carrier Add scripts
		
					if(sites.size() > 1) {
						Set<String> isExternalNrNodePresent = new HashSet<String>();;
						for(String node: sites) {
							String siteStr = duInfo.duName.replaceAll("^[A-Za-z]", "").replaceAll("[\\d]+$", "");
							if(!node.equals(duInfo.duName) && node.matches(".*" + siteStr + ".*") && (node.startsWith("N") || node.startsWith("M"))) {
								isExternalNrNodePresent.add(node);
							}
						}
						if(isExternalNrNodePresent != null && !isExternalNrNodePresent.isEmpty())	{
							//For generate NR - NR relation scripts.
							if(duInfo.tmoDUInfo.triggerNR2NRRelationScript) {
								for (String nrNodeName : isExternalNrNodePresent) {
									SiteCellObj nrDuInfo = new SiteCellObj();
									if (duToDUInfo.containsKey(nrNodeName)) {
										nrDuInfo = duToDUInfo.get(nrNodeName);
									}
									
									if (nrDuInfo != null) {
										// Use these 2 as a trigger to include/exclude for TDD 2C carrier add
										nrDuInfo.nrnodename = nrNodeName;
										nrDuInfo.tdddulname = duInfo.duName;		// TDD node name (MMBB or N41 stand-alone)
										
										String fileNodeName = tmoFileRenamingForESI.calculcateFileFolderNodeName(nrDuInfo);
										String addDir = FileUtil.createDirReturnStr(siteDir + File.separator + fileNodeName);
										String nRToNRRelationScript = addDir + File.separator + "01_" + fileNodeName + "_NR71_To_NR41_Relation.mos";

										//NR71 To NR41 Relation Script
										String sourceNode = "N71";
										String targetNode = "N41";
										tmoCCR.generateNRToNRRelationScript(nrDuInfo, nRToNRRelationScript, sourceNode, targetNode);
									}
								}
							}
						}
					}
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateTddCarrierAddScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating TDD NR Carrier Add scripts!");
		}
	}	
	
	private void generateTDDRETScript(SiteCellObj duInfo, String OutputDir) {
		StringBuilder sb = new StringBuilder();
		
		sb.append("gs+" + eol
				+ "confb+" + eol
				+ "lt all" + eol);
		String digitalTilt="";
		if(duInfo != null && duInfo.tmoDUInfo.duToDeltaAddCells != null && duInfo.tmoDUInfo.duToDeltaAddCells.size()>0) {
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String currCellFddName = kvp.getKey();
				if(duInfo.tmoDUInfo.duToDeltaAddCells.contains(currCellFddName)) {
					String sectorEquipFunc = "";
					sectorEquipFunc = tmoDC.generateSectorEquipementFunction(currCellFddName);
					String sectorCarrierNumber = tmoCCR.generateMmbbSectorCarrierNumber(currCellFddName);
					digitalTilt= CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_" + CiqConstants.ciqSheetToCSVFileTag.get("eUtran Parameters")), "EutranCellFDDId",currCellFddName , "electricalAntennaTilt");
					if(digitalTilt!=null && !digitalTilt.isEmpty()) {
						sb.append("set ENodeBFunction=1,SectorCarrier=" + sectorEquipFunc + sectorCarrierNumber + "$" + " digitalTilt " + digitalTilt + eol);
					}
					else {
						sb.append("//set ENodeBFunction=1,SectorCarrier=" + sectorEquipFunc + sectorCarrierNumber + "$" + " digitalTilt " + digitalTilt + eol);
						Logger.logger.error(currCellFddName + " electricalAntennaTilt Value is missing/Empty on the RNDCIQ");
						Logger.getGmoLogger().printError(currCellFddName + " electricalAntennaTilt Value is missing/Empty on the RNDCIQ");
					}
				}
			}
		}
		
		if(duInfo != null) {
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String currCellFddName = kvp.getKey();
				SiteCellObj currCellObj = kvp.getValue();
				boolean blnCreateCommonBeamFormingBlock = (currCellFddName.startsWith("A")) ? true : false;
				if(blnCreateCommonBeamFormingBlock) {
					String currSecEquipFunc = duInfo.map5GCellFddNameToAugIdId.get(currCellFddName);
					String sectorCarrierNumber = tmoCCR.generateMmbbSectorCarrierNumber(currCellFddName);
					digitalTilt= CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_" + CiqConstants.ciqSheetToCSVFileTag.get("gUtranCell info")), "gUtranCell",currCellFddName , "electricalAntennaTilt");
					if(digitalTilt!=null && !digitalTilt.isEmpty()) {
						sb.append("set NRSectorCarrier=" + currSecEquipFunc+sectorCarrierNumber + ",CommonBeamforming=1$ digitalTilt " + digitalTilt + eol);
					}
					else {
						sb.append("//set NRSectorCarrier=" + currSecEquipFunc+sectorCarrierNumber + ",CommonBeamforming=1$ digitalTilt " + digitalTilt + eol);
						Logger.logger.error(currCellFddName + " electricalAntennaTilt Value is missing/Empty on the RNDCIQ");
						Logger.getGmoLogger().printError(currCellFddName + " electricalAntennaTilt Value is missing/Empty on the RNDCIQ");
					}
					
				}
			}
			sb.append("gs-" + eol
					+ "confb-" + eol);

			String OutputStr=OutputDir + File.separator + "01_" + duInfo.duName + File.separator + duInfo.duName + "_RET_TDD_Excalibur.mos";
			FileUtil.writeToFile(sb, OutputStr);
		}
	}

	/**
	 * Function to generate CPRI Remapping scripts
	 * @throws Exception
	 */
	private void generateCPRIRemappingScripts() throws Exception
	{
		try {		
			Map<String, SiteCellObj> duToDUInfo = tmoCCR.getDUToDUInfo();
			SiteCellObj duInfo = new SiteCellObj();
			for(String site: sites) {
				if (duToDUInfo.containsKey(site)) {
					duInfo = duToDUInfo.get(site);
				}
				if(duInfo != null && duInfo.tmoDUInfo.isCPRIRemappingProject) {
					if(hasDataPortMismatchSites) {
						TMOCPRIRemappingProject tmoCRPIRemappingProject = new TMOCPRIRemappingProject(this , duToDUInfo, site);
						if(duInfo.tmoDUInfo.getTriggerDataPortMismatchScript()) {
							tmoCRPIRemappingProject.moduleForDataPortChange(duInfo, outputDir);
						}
						else {
							Logger.getGmoLogger().printWarning("Script will not be generated for site " + duInfo.duName + " !");
						}
					}
					else {
						Set<String> setOfSites = TMODataCollector.calculateSiteListForCPRI(duToDUInfo, sites);
						TMODataCollector.calculateBaseBandType(duInfo);
						Set<String> tempSites = new HashSet<String>();
						if(setOfSites != null && !setOfSites.isEmpty() && setOfSites.contains(duInfo.duName)) {
							tempSites.add(duInfo.duName);
							TMOCPRIRemappingProject tmoCRPIRemappingProject = new TMOCPRIRemappingProject(this , duToDUInfo, tempSites, setOfSites);
							if((duInfo.duName.startsWith("L") && !duInfo.duName.matches(".*[\\d]+$")) || duInfo.tmoCPRIRemappingDUInfo.getIsAir6499CpriReMapping()) {
								boolean isHardStop = tmoCRPIRemappingProject.checkCPRIRemappingPrechecks(duInfo);
								if(!isHardStop) {
									tmoCRPIRemappingProject.moduleForCPRIRemapping(duInfo, outputDir);
								}else {
									continue;
								}
							}
						}
						else {
							Logger.getGmoLogger().printWarning("Site " + duInfo.duName + " will be skipped !");
						}
					}
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateCPRIRemappingScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating CRPI Re-Mapping scripts! " + e.getMessage());
		}
	}

	/**
	 * Function to generate New SCU configuration scripts
	 * @throws Exception
	 */
	private void generateNewSCUConfigurationScripts() throws Exception
	{
		try {
			TMOScuScripts tmoScuScripts = new TMOScuScripts(inputDir, siteList, outputDir, this);
			tmoScuScripts.generateScripts();
		}
		catch (Exception e) {
			Logger.logger.error("generateNewSCUConfigurationScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating New SCU configuration scripts! " + e.getMessage());
		}
	}
	
	private void generateNewSCUConfigurationScriptsForTest() throws Exception {		// TC_395 part 2
		boolean triggerScript = false;
		Set<String> setOfSites = new HashSet<String>();
		try {
			boolean doesKgetExists = TMODataCollector.checkIfKgetExistsInInputDirectory();
			triggerScript = tmoDC.calculateTriggerForScuScript(siteList, ciqs);
			
			if((ciqs.containsKey("ATND") && ciqs.get("ATND").exists()) && (ciqs.containsKey("RND") && ciqs.get("RND").exists()) && doesKgetExists) {
				for(String site: sites) {
					String siteSubStr = site.replaceAll("^[A-Za-z]", "").replaceAll("[\\d]$", "");
					setOfSites.add(siteSubStr);
					if(!tmoCCR.getDUToDUInfo().containsKey(siteSubStr)) {
						SiteCellObj duInfo = new SiteCellObj();
						duInfo.duName = siteSubStr;
						duInfo.tmoDUInfo.isNewSCUConfiguration = true;
						
				
						// TC_395 Feedback
						HashMap<String, String> duRowData = CSVUtils.readDataRowFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_RND"), "eNodeB Name", site);
						if (duRowData == null || duRowData.isEmpty()) {
							duRowData = CSVUtils.readDataRowFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_ENBINFO"), "eNodeB Name", site);
						}

						// if the data from the RND ENB Info is blank, try to see if you can get from RND GNB Info sheet (5G RND CIQ)
						if (duRowData == null || duRowData.isEmpty()) {
							duRowData = CSVUtils.readDataRowFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GNBINFO"), "gNB Name", site);
							if(duRowData == null || duRowData.isEmpty()) {
								duInfo.is5G = false;
							}
							else {
								duInfo.is5G = true;
							}
						}
						else
						{
							duInfo.is5G = false;
						}// TC_395 Feedback
						
						
						tmoDC.collectSiteDataForSCU(duInfo);
						tmoCCR.getDUToDUInfo().put(duInfo.duName, duInfo);
					}
				}
				
				if(triggerScript) {		// TC_395 part 2
					TMOScuScripts tmoScuScripts = new TMOScuScripts(inputDir, setOfSites, outputDir, this);
					tmoScuScripts.generateScripts();
				}
				
			for(String site: setOfSites) {		// TC_395 part 2
				if(tmoCCR.getDUToDUInfo().containsKey(site)) {
					    tmoCCR.getDUToDUInfo().remove(site);
			        }
				}
			}
			else if((((ciqs.containsKey("ATND") && ciqs.get("ATND").exists()) && !ciqs.containsKey("RND") && !ciqs.containsKey("EXISTING_SCU_DATA")) 		// TC_395 part 2
						|| (ciqs.containsKey("EXISTING_SCU_DATA") && ciqs.get("EXISTING_SCU_DATA").exists() && (!ciqs.containsKey("ATND") || !ciqs.get("ATND").exists()) && !ciqs.containsKey("RND"))) && !doesKgetExists){
				TMOScuScripts tmoScuScripts = new TMOScuScripts(inputDir, siteList, outputDir, this);
				tmoScuScripts.generateScripts();
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateNewSCUConfigurationScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating New SCU configuration scripts! " + e.getMessage());
		}
	}
	

	/**
	 * Function to generate IPSec scripts for S2G
	 * @throws Exception
	 */
	private void generateIPSecScripts() throws Exception
	{
		try {
			TMOIPSecScripts tmoIPSecScripts = new TMOIPSecScripts(inputDir, siteList, outputDir, this);
			tmoIPSecScripts.generateScripts();
		}
		catch (Exception e) {
			Logger.logger.error("generateIPSecScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating IPSec scripts! " + e.getMessage());
		}
	}

	/**
	 * Function to generate NSB scripts, called by TMOIPSecScripts
	 * @throws Exception
	 */
	public void generateNewSiteBuildScripts() throws Exception
	{
		try {
			generateNSBScripts();
		}
		catch (Exception e) {
			Logger.logger.error("generateNewSiteBuildScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating NSB scripts! " + e.getMessage());
		}
	}

	/**
	 * Function to generate Anchor 2nd Cabinet scripts
	 * @throws Exception
	 */
	// TC_378, Removed call from NSB. Will duplicate, update method in MultiDUSectorAddLTEScriptsTMobile to generate script via Multi-DU option
	private void generateAnchorCabinet2Scripts() throws Exception
	{
		try {
			boolean legacyCabinet2 = false;		// Legacy LTE node has 2 cabinets
			boolean moveCabinet2 = false;		// Delete cabinet 2 from Legacy node
			boolean addCabinet2 = false;		// Add cabinet 2 to new Anchor node
			String legacyNodeName = "";
			
			Map<String, SiteCellObj> duToDUInfo = tmoCCR.getDUToDUInfo();
			/*// [01262021] Changed to read duToDUInfo instead of sites for case of data is collected for all nodes in sitelist but for Anchor, Multi-Du option calling NSB option, the sitelist is temporary reduced to only the NSB node name. But will need to create scripts for legacy LTE node (not in temporary sitelist).
			for(Entry<String, SiteCellObj> duInfoEntry : duToDUInfo.entrySet()) {
				SiteCellObj duInfo = duInfoEntry.getValue();*/
			for(String site: sites) {					// Works if both legacy and NSB anchor node is in sitelist, including during data collection. Does not work in current case of Multi-Du called NSB with on anchor node in sitelist and data collection
 				if (duToDUInfo.containsKey(site)) {
					SiteCellObj duInfo = duToDUInfo.get(site);
					if (duInfo != null) {	// Is Anchor scope
						String duNameForKgetLookup = TMO_CommonUtil.getDuNameForKgetLookup(duInfo);
						if(duInfo.duName.contentEquals(duNameForKgetLookup) && duInfo.cabinet.matches(".*2.*")) {	// Cabinet 2 exists in kget of legacy node
							legacyCabinet2 = true;
							legacyNodeName = duNameForKgetLookup;
						}
						else if (duInfo.getSiteObj().isIs4gAnchor() && duInfo.isNewSite) {	// Check if new Anchor node needs cabinet swap
							if (duInfo.rbsType.contains("6160")) {							// if Anchor node shows cabinet swap to 6160 (Read from CIQ) then generate Legacy node E28 delete cabinet 2 scripts
								moveCabinet2 = true;
							}
							else if (duInfo.rbsType.matches(".*(6102|6201).*")) {			//if Anchor node shows no cabinet swap i.e. 6102 or 6201 (Read from CIQ) then generate Legacy node E28 scripts & Anchor node E41a add cabinet 2 scripts
								moveCabinet2 = true;
								addCabinet2 = true;
							}
						}
					}
				}
			}

			String siteDir = "";
//			for (String site : sites) {
//				SiteCellObj duInfo = duToDUInfo.get(site);
			for(Entry<String, SiteCellObj> duInfoEntry : duToDUInfo.entrySet()) {	// [01262021]
				SiteCellObj duInfo = duInfoEntry.getValue();
				String site = duInfo.duName;
				if (legacyCabinet2 && moveCabinet2) {
					String duNameForKgetLookup = TMO_CommonUtil.getDuNameForKgetLookup(duInfo);

					siteDir = FileUtil.createDirReturnStr(outputDir + File.separator + String.join("_", sites) + File.separator + "01_" + site);
					
					if (duInfo.duName.contentEquals(duNameForKgetLookup)) {
						generateCabinet1DeletionScript(duInfo, siteDir, "DOS");
					}
					else if ((duInfo.getSiteObj().isIs4gAnchor() || duInfo.tmoDUInfo.isTDDNode) && duInfo.isNewSite) {

						// Initialize ParamPreservation object for Cabinet, Anchor SOW
						ParamPreservation pp = new ParamPreservation();
						pp.setSite(site);
						pp.setSoftwareLevel(duInfo.softwareLevel);
						pp.setBBU(duInfo.isBBU);
						pp.setInputFormat(duInfo.inputFormat);
						pp.setOutputFormat(duInfo.outputFormat);
						pp.setMarket(duInfo.getSiteObj().getMarket());
						pp.setTmoCCR(tmoCCR);
						pp.initializeGeneric();

						generateCabinet2ModificationBlock(duInfo, legacyNodeName, siteDir, pp, "DOS");
					}
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateAnchorCabinet2Scripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating Anchor Cabinet 2 scripts!");
		}
	}

	private void generate5GNR600RiLinkScriptForNGS(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			sb.append("confb+" + eol);
			sb.append("gs+" + eol);
			sb.append(eol);
			sb.append("lt all" + eol);
			sb.append(eol);

			sb.append("#Create RiLink" + eol);
			Integer count = 0;
			char [] arrRiPortNames = new char[] {' ', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'J'};		// [08262019] Added D in case of cellid 2,3,4 instead of 1,2,3, [09102019] Added E to J, skipping I
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String currCellFddName = kvp.getKey();
				count++;

				String currSecEquipFunc = "6-0" + kvp.getValue().cellId;	// [08272019] Use RNDCIQ cellid as it may be different from kget existing id
				String futureSecEquipFunc = "";
				for(Entry<String, String> fruIdTo5GCellFddName : duInfo.hash5GKgetFruIdTo5GCellFddNameMap.entrySet()) {
					if(fruIdTo5GCellFddName.getValue().equals(currCellFddName)) {
						futureSecEquipFunc = fruIdTo5GCellFddName.getKey();
						break;
					}
				}
				if(!futureSecEquipFunc.isEmpty()) {
					currSecEquipFunc = futureSecEquipFunc;
				}

				if(currSecEquipFunc.replace("6-0", "").isEmpty()) {						// [08272019]
					Logger.getGmoLogger().printWarning("Could not get AntennaUnitGroup ID for cell [" + currCellFddName + "]. Skipping this cell's info from the RiLink script! Please check the scripts!!! ");

					continue;
				}
				int secEquipFuncLastDigit = Integer.parseInt(currSecEquipFunc.substring(currSecEquipFunc.length() - 2));		// [09112019] Updated to get last 2 digits
				// [08142019 - eusxjas] Currently only 3 sectors is supported by software. If 4 sectors are found in L600, then give a warning message
				// [08260219 - eusxjas] Added check for counting size > 3 in case the cellid/last digit starts at 2 (expected cells 2,3,4) instead of 1
				Integer maxSupportSect = 9;		// [09102019] Added support for upto 9 sectors, was 3
				if(duInfo.newCellToCellInfo.size() > maxSupportSect && (count == duInfo.newCellToCellInfo.size())) { // Give message only for specific cells that are above expected range/count
					Logger.getGmoLogger().printWarning("5G software currently supports a maximum of " + maxSupportSect + "  sectors for NGS! RND shows " + duInfo.newCellToCellInfo.size() + " sectors.");
				}

				int maxIndexUsed = 0;		// TC_212 [09182019]
				if(secEquipFuncLastDigit <= maxSupportSect) { 	// [08262019] Check to insure RiPort standard sequence range is not exceeded
					char riPortName = arrRiPortNames[secEquipFuncLastDigit];
					maxIndexUsed = secEquipFuncLastDigit > 3 ? Integer.max(maxIndexUsed + 1, 4) : Integer.max(maxIndexUsed, secEquipFuncLastDigit);		// [09252019] In case sectors 1-3 are skipped, sectors 4+ will start from 4th index and next higher
					riPortName = (secEquipFuncLastDigit > 3) ? arrRiPortNames[maxIndexUsed] : riPortName;	// [09112019] First 3 sectors should be A, B or C even if skipped sector, 4th sector and above should be in sequence D,E,F even if skipped sector (this is due to cabling done in advance)
					sb.append(eol);
					sb.append("pr Equipment=1,RiLink=BB-01-" + riPortName + "-" + currSecEquipFunc + "-Data2" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,RiLink=BB-01-" + riPortName + "-" + currSecEquipFunc + "-Data2" + eol);
					sb.append("FieldReplaceableUnit=BB-01,RiPort=" + riPortName + eol);
					sb.append("FieldReplaceableUnit=" + currSecEquipFunc + ",RiPort=DATA_2" + eol);
					sb.append("fi" + eol);
				}
				else {
					Logger.getGmoLogger().printWarning("5G " + duInfo.duName + ", cellid " + secEquipFuncLastDigit + " is not mapped to a RiPort for RiLink.");
				}
			}

			sb.append(eol);
			sb.append("gs-" + eol);
			sb.append("confb-" + eol);

			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNR600RiLinkScriptForNGS exception!", ex);
			Logger.getGmoLogger().printError("Error generating 5G NR600 RiLink script for NGS! " + ex.getMessage());
		}
	}

	private void generate5GNR600DeltaDeleteScript(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			sb.append("Confbdl+" + eol);
			sb.append("gs+" + eol);
			sb.append(eol);

//			{	// TC_361
			String nodeType = (duInfo.isBBU || duInfo.nodeType.matches("BB.*") || duInfo.outputFormat.contentEquals("G2")) ? "BB" : duInfo.nodeType;
			sb.append(tmoCCR.generateGenericNodeNameBlock(duInfo.duName, nodeType));		// [10272020]
//			}
//			else {
//				sb.append(tmoCCR.generateGenericFingerPrintBlock(duInfo.duName));	// [05152020]
//			}

			String strFirst5GCell = duInfo.kgetCellFddIds.get(0);
			String strTrimmedCellFddName = strFirst5GCell.substring(0, strFirst5GCell.length() - 2);

			sb.append("u+" + eol);
			sb.append("del RiLink=BB-01-D-6-0" + eol);
			sb.append("bl NRCellDU=" + strTrimmedCellFddName + "[456789]1$" + eol);
			sb.append("del NRCellDU=" + strTrimmedCellFddName + "[456789]1$" + eol);
			sb.append("del NRCellCU=" + strTrimmedCellFddName + "[456789]1$" + eol);
			sb.append("bl NRSectorCarrier=6-0[456789]" + eol);
			sb.append("del NRSectorCarrier=6-0[456789]" + eol);
			sb.append(genericScriptBlockGenerator.generateSectEquipFuncBlockCmd() + "6-0[456789]" + eol);
			sb.append("del SectorEquipmentFunction=6-0[456789]" + eol);
			sb.append("rdel AntennaUnitGroup=6-0[456789]" + eol);
			sb.append("rdel FieldReplaceableUnit=6-0[456789]" + eol);
			sb.append("u-" + eol);
			sb.append(eol);
			sb.append("wait 2" + eol);


			sb.append("gs-" + eol);
			sb.append("Confbdl-" + eol);
			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNR600DeltaDeleteScript exception!", ex);
			Logger.getGmoLogger().printError("Error generating 5G NR600 Delta Delete script! ");
		}
	}

	private void generateCarrierAdd01Script(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{	
			sb.append("Confbdl+" + eol);
			sb.append("gs+" + eol);
			sb.append(eol);

			// TC_361
			String nodeType = (duInfo.isBBU || duInfo.nodeType.matches("BB.*") || duInfo.outputFormat.contentEquals("G2")) ? "BB" : duInfo.nodeType;
			sb.append(tmoCCR.generateGenericNodeNameBlock(duInfo.duName, nodeType));		// [10272020]
			
			sb.append("//////// RRU" + eol);
			sb.append(eol);

			List<String> lstFruIdListToBeUsed = new ArrayList<String>();
			if(duInfo.rndFieldReplaceableUnitIds5g.size() > 0) {
				lstFruIdListToBeUsed = duInfo.rndFieldReplaceableUnitIds5g;
			}
			else {
				lstFruIdListToBeUsed = duInfo.kgetFieldReplaceableUnitIds5g;
			}

			sb.append(eol);

			// Add a delete command for those FieldReplaceableUnit (FRU) IDs that are in KGet but not in RND.
			for(String strCurrFruIdInKGet : duInfo.kgetFieldReplaceableUnitIds5g) {
				if(!duInfo.rndFieldReplaceableUnitIds5g.contains(strCurrFruIdInKGet)) {
					sb.append("del Equipment=1,FieldReplaceableUnit=" + strCurrFruIdInKGet + "$" + eol);
				}
			}
			sb.append(eol);

			if( duInfo.isMmWave) {	//TMO_202
			}
			else {
				// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
				lstFruIdListToBeUsed = duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation?tmoDC.updateFruIdListCarrierAdd(duInfo) : lstFruIdListToBeUsed;
			}
				
			for(String strCurrFruIdInKGet : lstFruIdListToBeUsed) {
				String strCurrAugId = strCurrFruIdInKGet;

				String strDlAttenuationValToUse = "3";
				String strUlAttenuationValToUse = "3";
				String strDlTrafficDelayValToUse = "115";
				String strUlTrafficDelayValToUse = "115";

				if(duInfo.hash5GKgetFruIdTo5GCellFddNameMap.get(strCurrAugId) != null) {
					try {
						String strCellFddNameForCurrAugId = duInfo.hash5GKgetFruIdTo5GCellFddNameMap.get(strCurrAugId);
						if(!duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.dlTrafficDelay.trim().equals("")) {
							strDlTrafficDelayValToUse = duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.dlTrafficDelay;
						}

						if(!duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.ulTrafficDelay.trim().equals("")) {
							strUlTrafficDelayValToUse = duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.ulTrafficDelay;
						}

						if(!duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.dlAttenuation.trim().equals("")) {
							strDlAttenuationValToUse = duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.dlAttenuation;
						}

						if(!duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.dlTrafficDelay.trim().equals("")) {
							strUlAttenuationValToUse = duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.ulAttennuation;
						}
					}
					catch(Exception ex) {
						Logger.getGmoLogger().printError("Could not compute the delay and attenuation values to be used from RND. Please check your scripts.");
					}
				}
				boolean blnAddFruCreationBlock = false;
				if(!duInfo.kgetFieldReplaceableUnitIds5g.contains(strCurrAugId)) {
					blnAddFruCreationBlock = true;
				}

				// #TC_210
				blnAddFruCreationBlock = true;
				// #TC_197
				// add FieldReplaceableUnit MO for Those IDs that are in RND but not in KGet.
				if(blnAddFruCreationBlock) {
					sb.append(eol);
					sb.append(eol);
					sb.append("//////// FieldReplaceableUnit=" + strCurrAugId + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + "$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + eol);
					sb.append("administrativeState 1" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					String comment = (duInfo.isNR600) ? "//" : "";
					sb.append(comment + "set Equipment=1,FieldReplaceableUnit=" + strCurrAugId + "$ isSharedWithExternalMe true" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_1" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_1" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_2" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_2" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
						sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_3" + eol);
						sb.append("if $nr_of_mos = 0" + eol);
						sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_3" + eol);
						sb.append("end" + eol);
						sb.append("fi" + eol);
						sb.append(eol);
						if(duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
							sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_4" + eol);
							sb.append("if $nr_of_mos = 0" + eol);
							sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_4" + eol);
							sb.append("end" + eol);
							sb.append("fi" + eol);
							sb.append(eol);
						}
						sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",Transceiver=1" + eol);
						sb.append("if $nr_of_mos = 0" + eol);
						sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",Transceiver=1" + eol);
						sb.append("end" + eol);
						sb.append("fi" + eol);
					}else {
						sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=A" + eol);
						sb.append("if $nr_of_mos = 0" + eol);
						sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=A" + eol);
						sb.append("end" + eol);
						sb.append("fi" + eol);
						sb.append(eol);
						sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=B" + eol);
						sb.append("if $nr_of_mos = 0" + eol);
						sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=B" + eol);
						sb.append("end" + eol);
						sb.append("fi" + eol);
						sb.append(eol);
						sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=C" + eol);
						sb.append("if $nr_of_mos = 0" + eol);
						sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=C" + eol);
						sb.append("end" + eol);
						sb.append("fi" + eol);
						sb.append(eol);
						sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=D" + eol);
						sb.append("if $nr_of_mos = 0" + eol);
						sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=D" + eol);
						sb.append("end" + eol);
						sb.append("fi" + eol);
					}
					sb.append(eol);
					sb.append("WAIT 5" + eol);
					sb.append(eol);
				}

				String dlTrafficDelayForPrint = new String(new char[15]).replace("\0", strDlTrafficDelayValToUse + " ");
				String ulTrafficDelayForPrint = new String(new char[15]).replace("\0", strUlTrafficDelayValToUse + " ");
				String dlAttenuationForPrint = new String(new char[15]).replace("\0", strDlAttenuationValToUse + " ");
				String ulAttenuationForPrint = new String(new char[15]).replace("\0", strUlAttenuationValToUse + " ");
				if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					sb.append(eol);
					sb.append(eol);
					sb.append("///////    AntennaUnitGroup=" + strCurrAugId + eol);
					sb.append(eol);
					sb.append(eol);

					sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + "$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=0" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=0" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=3" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=3" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}

				if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					sb.append("// Create RfBranch" + eol);
					sb.append(eol);

					// RfBranch 1
					sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=1$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=1" + eol);
					sb.append("dlAttenuation " + dlAttenuationForPrint + eol);
					sb.append("dlTrafficDelay " + dlTrafficDelayForPrint + eol);
					sb.append("ulAttenuation " + ulAttenuationForPrint + eol);
					sb.append("ulTrafficDelay " + ulTrafficDelayForPrint + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);

					sb.append("// Set rfPortRef" + eol);
					sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=1 rfPortRef Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=A" + eol);
					sb.append(eol);

					sb.append("// Set auPortRef" + eol);
					sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=1 auPortRef AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=0" + eol);
					sb.append(eol);

					// RfBranch 2
					sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=2$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=2" + eol);
					sb.append("dlAttenuation " + dlAttenuationForPrint + eol);
					sb.append("dlTrafficDelay " + dlTrafficDelayForPrint + eol);
					sb.append("ulAttenuation " + ulAttenuationForPrint + eol);
					sb.append("ulTrafficDelay " + ulTrafficDelayForPrint + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);

					sb.append("// Set rfPortRef" + eol);
					sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=2 rfPortRef Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=C" + eol);
					sb.append("// Set auPortRef" + eol);
					sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=2 auPortRef AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2" + eol);
					sb.append(eol);

					// RfBranch 3
					sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=3$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=3" + eol);
					sb.append("dlAttenuation " + dlAttenuationForPrint + eol);
					sb.append("dlTrafficDelay " + dlTrafficDelayForPrint + eol);
					sb.append("ulAttenuation " + ulAttenuationForPrint + eol);
					sb.append("ulTrafficDelay " + ulTrafficDelayForPrint + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("// Set rfPortRef" + eol);
					sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=3 rfPortRef Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=B" + eol);
					sb.append(eol);
					sb.append("// Set auPortRef" + eol);
					sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=3 auPortRef AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1" + eol);
					sb.append(eol);

					// RfBranch 4
					sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=4$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=4" + eol);
					sb.append("dlAttenuation " + dlAttenuationForPrint + eol);
					sb.append("dlTrafficDelay " + dlTrafficDelayForPrint + eol);
					sb.append("ulAttenuation " + ulAttenuationForPrint + eol);
					sb.append("ulTrafficDelay " + ulTrafficDelayForPrint + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("// Set rfPortRef" + eol);
					sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=4 rfPortRef Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=D" + eol);
					sb.append(eol);
					sb.append("// Set auPortRef" + eol);
					sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=4 auPortRef AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=3" + eol);
					sb.append(eol);
				}
			}
			
			//TC_295 - Add Rilink Create Portion for NR600/N41
			if(duInfo.isNR600) {
				sb.append("############################" + eol);
				sb.append("####### Create RiLink ######" + eol);
				sb.append("############################" + eol + eol);
				List<String> lstFruIdsToUse = duInfo.kgetFieldReplaceableUnitIds5g;
				if(duInfo.rndFieldReplaceableUnitIds5g != null && duInfo.rndFieldReplaceableUnitIds5g.size() > 0)	{
					lstFruIdsToUse = duInfo.rndFieldReplaceableUnitIds5g;
				}
				if(lstFruIdsToUse==null || lstFruIdsToUse.size() == 0) {
					lstFruIdsToUse = new ArrayList<String>();
					lstFruIdsToUse.add("6-01");
					lstFruIdsToUse.add("6-02");
					lstFruIdsToUse.add("6-03");
				}

				
				
				String [] arrFruIdToNumberingMap = new String [] {" ", "A", "B", "C", "D", "E"};


				for(String strCurrFruId : lstFruIdsToUse) {
					int fruIdIndex = Integer.parseInt(strCurrFruId.substring(strCurrFruId.length() - 1));
					sb.append("pr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-Data2" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-Data2" + eol);
					sb.append("FieldReplaceableUnit=BB-01,RiPort=" + arrFruIdToNumberingMap[fruIdIndex] + eol);
					sb.append("FieldReplaceableUnit=" + strCurrFruId + ",RiPort=DATA_2" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
				
				sb.append("wait 5" + eol + eol);
			}

			if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
				sb.append("############################" + eol);
				sb.append("####### Create RiLink ######" + eol);
				sb.append("############################" + eol + eol);
				// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
				if (duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation) {
					sb.append(tmoDC.genericBlockRiLinkDeleteCarrierAdd());
				}
				List<String> lstFruIdsToUse = duInfo.kgetFieldReplaceableUnitIds5g;
				if(duInfo.rndFieldReplaceableUnitIds5g != null && duInfo.rndFieldReplaceableUnitIds5g.size() > 0)	{
					lstFruIdsToUse = duInfo.rndFieldReplaceableUnitIds5g;
				}
				if (duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation) {
					Collections.sort(lstFruIdsToUse);
				}
				String [] arrFruIdToNumberingMap = new String [] {};
				if(duInfo.isMmWave) { //TMO_202
					arrFruIdToNumberingMap = new String [] { "A", "B", "E", "F", "J", "K"};
					
				}
				else 
					if(duInfo.tmoDUInfo.getIsMidBandAnchorScopeWith6449Radio() || duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation) {
				
					//Only N41 with BB6648 support all the 4 sectors on the same node
					arrFruIdToNumberingMap = new String [] {"A", "B", "C", "D", "E", "F", "G", "H"};
				}else {
					arrFruIdToNumberingMap = new String [] {"A", "B", "C", "D", "E", "F"};
				}
				
				
				for(String strCurrFruId : lstFruIdsToUse) {
					int fruIdIndex = lstFruIdsToUse.indexOf(strCurrFruId);
					String dataPort1 = "";
					String dataPort2 = "";
					String riPort = "";
					
					//[11202020] - AIR 6499 with DATA_2 and DATA_3
					if(duInfo.isMmWave ) { //[12072021] -TMO_202
						dataPort1 = "Data1";
						riPort = "DATA_1";
					}else {
						dataPort1 = "Data2";
						riPort = "DATA_2";
					}
					sb.append("pr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-" + dataPort1 + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-" + dataPort1 + eol);
					sb.append("FieldReplaceableUnit=BB-01,RiPort=" + arrFruIdToNumberingMap[fruIdIndex] + eol);
					sb.append("FieldReplaceableUnit=" + strCurrFruId + ",RiPort=" + riPort + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					//[11202020] - AIR 6499 with DATA_2 and DATA_3
//					if(duInfo.tmoDUInfo.getIsMidBandAnchorScopeWith6449Radio()) {
//						dataPort2 = "Data4";
//						riPort = "DATA_4";
//					}else {
					//[12072021] -TMO-202
					//[11202020] - AIR 6499 with DATA_2 and DATA_3
					if(duInfo.isMmWave ) {//[12072021] -TMO_202
						dataPort2 = "Data2";
						riPort = "DATA_2";
					}else {
					
						dataPort2 = "Data3";
						riPort = "DATA_3";
					}
					arrFruIdToNumberingMap = (String[]) ArrayUtils.remove(arrFruIdToNumberingMap, fruIdIndex);
					sb.append("pr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-" + dataPort2 + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-" + dataPort2 + eol);
					sb.append("FieldReplaceableUnit=BB-01,RiPort=" + arrFruIdToNumberingMap[fruIdIndex] + eol);
					sb.append("FieldReplaceableUnit=" + strCurrFruId + ",RiPort=" + riPort + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
				sb.append("wait 5" + eol + eol);
			}
			
			sb.append("//////////////////////" + eol);
			sb.append("///    Sector      ///" + eol);
			sb.append("//////////////////////" + eol);
			sb.append(eol);

			for(String strCurrFruIdInKGet : lstFruIdListToBeUsed) {
				String strCurrAugId = strCurrFruIdInKGet;
				sb.append(eol);
				sb.append("pr NodeSupport=1,SectorEquipmentFunction=" + strCurrAugId + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn NodeSupport=1,SectorEquipmentFunction=" + strCurrAugId + eol);
				sb.append("administrativeState 1" + eol);
				if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					sb.append("rfBranchRef Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",Transceiver=1" + eol);
				}else {
					sb.append("rfBranchRef Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=1 Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=2 Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=3 Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=4" + eol);
				}
				sb.append("end" + eol);
				sb.append("fi" + eol);

			}
			sb.append(eol);

			// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
			boolean blnServiceDiscoveryMO = duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation ? false : true;
			if (blnServiceDiscoveryMO) {
				sb.append("######################################" + eol);
				sb.append("# Create ServiceDiscovery MO, if needed" + eol);
				sb.append("######################################" + eol);
				sb.append(eol);
				sb.append(eol);
				sb.append("get SystemFunctions=1,SysM=1,NetconfTls=1 nodeCredential > $NCValue" + eol);
				sb.append("get SystemFunctions=1,SysM=1,NetconfTls=1 trustCategory > $TCValue" + eol);
				sb.append(eol);
				sb.append(eol);
				sb.append("pr ServiceDiscovery=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn NodeSupport=1,ServiceDiscovery=1" + eol);


				sb.append("primaryGsds host=localhost,port=8301,serviceArea=NR" + eol);
				sb.append("secondaryGsds" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("set NodeSupport=1,ServiceDiscovery=1 nodeCredential $NCValue" + eol);
				sb.append("set NodeSupport=1,ServiceDiscovery=1 trustCategory $TCValue" + eol);
				sb.append(eol);
				sb.append(eol);


				// #TC_210
				sb.append("pr Transport=1,SctpProfile=1$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,SctpProfile=1" + eol);
				sb.append("alphaIndex 3" + eol);
				sb.append("assocMaxRtx 8" + eol);
				sb.append("betaIndex 2" + eol);
				sb.append("bundlingActivated false" + eol);
				sb.append("bundlingAdaptiveActivated true" + eol);
				sb.append("bundlingTimer 10" + eol);
				sb.append("cookieLife 60" + eol);
				sb.append("dscp 24" + eol);
				sb.append("hbMaxBurst 1" + eol);
				sb.append("heartbeatActivated true" + eol);
				sb.append("heartbeatInterval 30000" + eol);
				sb.append("incCookieLife 30" + eol);
				sb.append("initARWnd 32768" + eol);
				sb.append("initRto 1000" + eol);
				sb.append("initialHeartbeatInterval 5000" + eol);
				sb.append("maxActivateThr 65535" + eol);
				sb.append("maxBurst 4" + eol);
				sb.append("maxInStreams 4" + eol);
				sb.append("maxInitRt 12" + eol);
				sb.append("maxOutStreams 4" + eol);
				sb.append("maxRto 2000" + eol);
				sb.append("maxSctpPduSize 556" + eol);
				sb.append("maxShutdownRt 5" + eol);
				sb.append("minActivateThr 1" + eol);
				sb.append("minRto 500" + eol);
				sb.append("noSwitchback false" + eol);
				sb.append("pathMaxRtx 8" + eol);
				sb.append("primaryPathAvoidance false" + eol);
				sb.append("primaryPathMaxRtx 8" + eol);
				sb.append("sackTimer 20" + eol);
				sb.append("thrTransmitBuffer 192" + eol);
				sb.append("thrTransmitBufferCongCeased 85" + eol);
				sb.append("transmitBufferSize 256" + eol);
				sb.append("userLabel 1" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				
				String sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_X2" : "1";
				sb.append("pr Transport=1,SctpEndpoint=" + sctpEndPointId + "$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,SctpEndpoint=" + sctpEndPointId + eol);
				sb.append("localIpAddress Transport=1,Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
				sb.append("portNumber 36422" + eol);
				sb.append("sctpProfile Transport=1,SctpProfile=1" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("pr Transport=1,Router=Node_Internal_F1$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,Router=Node_Internal_F1" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("pr Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRCUCP$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRCUCP" + eol);
				sb.append("loopback true" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("pr Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRDU$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRDU" + eol);
				sb.append("loopback true" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("pr Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRCUCP,AddressIPv4=1$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRCUCP,AddressIPv4=1" + eol);
				sb.append("address 169.254.42.42/32" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("pr Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRDU,AddressIPv4=1$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRDU,AddressIPv4=1" + eol);
				sb.append("address 169.254.42.43/32" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("pr Transport=1,SctpProfile=Node_Internal_F1$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,SctpProfile=Node_Internal_F1" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("pr Transport=1,SctpEndpoint=F1_NRCUCP$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,SctpEndpoint=F1_NRCUCP" + eol);
				sb.append("localIpAddress Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRCUCP,AddressIPv4=1" + eol);
				sb.append("portNumber 38472" + eol);
				sb.append("sctpProfile Transport=1,SctpProfile=Node_Internal_F1" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("pr Transport=1,SctpEndpoint=F1_NRDU$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,SctpEndpoint=F1_NRDU" + eol);
				sb.append("localIpAddress Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRDU,AddressIPv4=1" + eol);
				sb.append("portNumber 38472" + eol);
				sb.append("sctpProfile Transport=1,SctpProfile=Node_Internal_F1" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);

				sb.append(eol);

				if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || duInfo.isNR600 || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					sb.append("###################################" + eol);
					sb.append("# SCTP endpoint used by the GNodeBFunction" + eol);
					sb.append("###################################" + eol);
					sb.append(eol);
					
					sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_X2" : "1";
					sb.append("pr Transport=1,SctpEndpoint=" + sctpEndPointId + "$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Transport=1,SctpEndpoint=" + sctpEndPointId + eol);
					sb.append("localIpAddress Transport=1,Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
					sb.append("portNumber 36422" + eol);
					sb.append("sctpProfile Transport=1,SctpProfile=1" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					
					sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_N2" : "2";
					sb.append("pr Transport=1,SctpEndpoint=" + sctpEndPointId + "$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Transport=1,SctpEndpoint=" + sctpEndPointId + eol);
					sb.append("localIpAddress Transport=1,Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
					sb.append("portNumber 38412" + eol);
					sb.append("sctpProfile Transport=1,SctpProfile=1" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					
					sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_Xn" : "xn";
					sb.append("pr Transport=1,SctpEndpoint=" + sctpEndPointId + "$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Transport=1,SctpEndpoint=" + sctpEndPointId + eol);
					sb.append("localIpAddress Transport=1,Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
					sb.append("portNumber 38422" + eol);
					sb.append("sctpProfile Transport=1,SctpProfile=1" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
			}

			// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
			boolean blnNode = duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation ? false : true;
			if (blnNode) {
				sb.append("//////////////////////" + eol);
				sb.append("/// Node           ///" + eol);
				sb.append("//////////////////////" + eol);
				sb.append(eol);
				sb.append("pr GNBDUFunction=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBDUFunction=1" + eol);
				if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.isNR600 && !(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					sb.append("f1SctpEndPointRef SctpEndpoint=F1_NRDU" + eol);
				}
				sb.append("gNBDUId 1" + eol);
				sb.append("gNBId " + duInfo.enbId + eol);
				sb.append("gNBIdLength 24" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || duInfo.isNR600 || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					sb.append("pr GNBDUFunction=1,EndpointResource=1" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBDUFunction=1,EndpointResource=1" + eol);
					sb.append("userLabel " + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					
					sb.append("set GNBDUFunction=1 endpointResourceRef GNBDUFunction=1,EndpointResource=1" + eol);
					sb.append(eol);
					
					sb.append("pr GNBDUFunction=1,EndpointResource=1,LocalSctpEndpoint=1" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBDUFunction=1,EndpointResource=1,LocalSctpEndpoint=1" + eol);
					sb.append("interfaceUsed 3" + eol);
					sb.append("sctpEndpointRef SctpEndpoint=F1_NRDU" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					
					sb.append("##################################################################################" + eol);
					sb.append(eol);
				}

				sb.append("pr GNBCUCPFunction=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1" + eol);
				if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.isNR600 && !(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					sb.append("f1SctpEndPointRef SctpEndpoint=F1_NRCUCP" + eol);
				}
				sb.append("gNBId " + duInfo.enbId + eol);
				sb.append("gNBIdLength 24" + eol);
				sb.append("pLMNId mcc=310,mnc=260" + eol);
				if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.isNR600 && !(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					String sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_X2" : "1";
					sb.append("x2SctpEndPointRef SctpEndpoint=" + sctpEndPointId + eol);
				}
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				
				if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || duInfo.isNR600 || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					sb.append("pr GNBCUCPFunction=1,EndpointResource=1" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,EndpointResource=1" + eol);
					sb.append("userLabel " + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					
					sb.append("set GNBCUCPFunction=1 endpointResourceRef GNBCUCPFunction=1,EndpointResource=1" + eol);
					sb.append(eol);
					
					String sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_Xn" : "xn";
					sb.append("pr GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=4" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=4" + eol);
					sb.append("interfaceUsed 6" + eol);
					sb.append("sctpEndpointRef SctpEndpoint=" + sctpEndPointId + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					
					sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_X2" : "1";
					sb.append("pr GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=3" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=3" + eol);
					sb.append("interfaceUsed 7" + eol);
					sb.append("sctpEndpointRef SctpEndpoint=" + sctpEndPointId + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					
					sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_N2" : "2";
					sb.append("pr GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=2" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=2" + eol);
					sb.append("interfaceUsed 4" + eol);
					sb.append("sctpEndpointRef SctpEndpoint=" + sctpEndPointId + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					
					sb.append("pr GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=1" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=1" + eol);
					sb.append("interfaceUsed 3" + eol);
					sb.append("sctpEndpointRef SctpEndpoint=F1_NRCUCP" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					
					sb.append("##################################################################################" + eol);
					sb.append(eol);
				}
				
				sb.append("pr GNBCUUPFunction=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUUPFunction=1" + eol);
				sb.append("gNBId " + duInfo.enbId + eol);
				sb.append("gNBIdLength 24" + eol);
				if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.isNR600 && !(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					sb.append("intraRanIpAddressRef Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
				}
				sb.append("pLMNIdList mcc=310,mnc=260" + eol);
				if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.isNR600 && !(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					sb.append("upIpAddressRef Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
				}
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				
				//[10222020]
				sb.append("pr GNBCUUPFunction=1,EndpointResource=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUUPFunction=1,EndpointResource=1" + eol);
				sb.append("userLabel " + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				
				sb.append("set GNBCUUPFunction=1 endpointResourceRef GNBCUUPFunction=1,EndpointResource=1" + eol);
				sb.append(eol);

				generateLocalIpEndpointMo(duInfo, sb, "vr_TRAFFIC", "1", eol);		// Refactored 7/1/2021 GMO_TMO-101

				sb.append("pr GNBDUFunction=1,TermPointToGNBCUCP=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBDUFunction=1,TermPointToGNBCUCP=1" + eol);
				sb.append("ipv4Address 169.254.42.42" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
			}

			sb.append("//////////////////////" + eol);
			sb.append("/// Sector Carrier ///" + eol);
			sb.append("//////////////////////" + eol);

			// map the AUG Ids to the cell IDs. Sort them alphabetically and then do a 1-to-1 mapping.
			sb.append(eol);
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String currCellFddName = kvp.getKey();
				SiteCellObj currCellObj = kvp.getValue();
				String currSecEquipFunc = duInfo.map5GCellFddNameToAugIdId.get(currCellFddName);
				// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
				boolean blnSectorEquipmentFunction = (duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation && !duInfo.tmoDUInfo.duToDeltaAddCells.contains(currCellObj.cellName) && !currCellObj.getCellObj().isMovingCell()) ? false : true;
				if (blnSectorEquipmentFunction) {
					if( duInfo.isMmWave) { //TMO_202
						sb.append("pr GNBDUFunction=1,NRSectorCarrier=" + currSecEquipFunc + "-0" + currCellFddName.charAt(currCellFddName.length()-1) + eol);
						sb.append("if $nr_of_mos = 0" + eol);
						sb.append("crn GNBDUFunction=1,NRSectorCarrier=" + currSecEquipFunc + "-0" + currCellFddName.charAt(currCellFddName.length()-1) + eol);
					}
					else {
					sb.append("pr GNBDUFunction=1,NRSectorCarrier=" + currSecEquipFunc + "-01" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBDUFunction=1,NRSectorCarrier=" + currSecEquipFunc + "-01" + eol);
					}
					sb.append("administrativeState 0" + eol);
					sb.append("arfcnDL " + currCellObj.earfcndl + eol);
					sb.append("arfcnUL " + currCellObj.earfcnul + eol);

					long intChBw = TMO_CommonUtil.convertChannelBwFor5G(currCellObj.channelBandwidth);

					sb.append("bSChannelBwDL " + intChBw + eol);
					sb.append("bSChannelBwUL " + intChBw + eol);
					//[08142020] Read configuredMaxTxPower value from RND irrespective of markets for NR600
					if (duInfo.isNR600 || duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
						sb.append("configuredMaxTxPower " + currCellObj.configuredOutputPower + eol);
					}
					sb.append("sectorEquipmentFunctionRef SectorEquipmentFunction=" + currSecEquipFunc + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
			}
			
			if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
				sb.append("/////////////////////////" + eol);
				sb.append("/// CommonBeamForming ///" + eol);
				sb.append("/////////////////////////" + eol);

				// map the AUG Ids to the cell IDs. Sort them alphabetically and then do a 1-to-1 mapping.
				sb.append(eol);
				for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
					String currCellFddName = kvp.getKey();
					SiteCellObj currCellObj = kvp.getValue();
					// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
					boolean blnCommonBeamForming = (duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation && !duInfo.tmoDUInfo.duToDeltaAddCells.contains(currCellObj.cellName) && !currCellObj.getCellObj().isMovingCell()) ? false : true;
					if (blnCommonBeamForming) {
						String digitalTilt = "";
						if(duInfo.subNetwork.matches("Syosset")) {
							digitalTilt = tmoDC.calculateDigitalTiltForMidAnchor(duInfo.duName, currCellFddName);
						}
						else if (duInfo.subNetwork.matches("Bloomfield")) {		// [01192022] GMO_TMO-218
							String electricalTilt = currCellObj.tmoCellInfo.electricalTilt;
							electricalTilt = electricalTilt.isEmpty() ? currCellObj.tmoCellInfo.electricalTiltForRet : electricalTilt;
							digitalTilt = electricalTilt;
						}
						else {
							digitalTilt = "30";
						}
						if (digitalTilt.isEmpty())	{		// [01192022] GMO_TMO-218
							Logger.getGmoLogger().printWarning("digitalTilt value not found for cell=" + currCellFddName + ", SubNetwork=" + duInfo.subNetwork + ". Please check CommonBeamforming in the script " + file);
						}

						String currSecEquipFunc = duInfo.map5GCellFddNameToAugIdId.get(currCellFddName);
						if(duInfo.isMmWave) //TMO_202
						{
							sb.append("pr GNBDUFunction=1,NRSectorCarrier=" + currSecEquipFunc + "-0" + currCellFddName.charAt(currCellFddName.length()-1) + ",CommonBeamforming=1" + eol);
							sb.append("if $nr_of_mos = 0" + eol);
							sb.append("crn GNBDUFunction=1,NRSectorCarrier=" + currSecEquipFunc + "-0" + currCellFddName.charAt(currCellFddName.length()-1) + ",CommonBeamforming=1" + eol);
						}
						else
						{
							sb.append("pr GNBDUFunction=1,NRSectorCarrier=" + currSecEquipFunc + "-01,CommonBeamforming=1" + eol);
							sb.append("if $nr_of_mos = 0" + eol);
							sb.append("crn GNBDUFunction=1,NRSectorCarrier=" + currSecEquipFunc + "-01,CommonBeamforming=1" + eol);
						}
						sb.append("cbfMacroTaperType 0" + eol);
						sb.append("coverageShape 0" + eol);
						sb.append("customComBfwWideBeam " + eol);
						sb.append("digitalPan " + eol);
						sb.append("digitalTilt " + digitalTilt + eol);
						sb.append("end" + eol);
						sb.append("fi" + eol);
						sb.append(eol);
					}
				}
			}

			sb.append("////////////" + eol);
			sb.append("/// Cell ///" + eol);
			sb.append("////////////" + eol);
			String [] arrRachRootSeq = new String[] {"", "0", "32", "64", "96", "96", "96", "96", "96", "96"};
			int cellCounter = 0;
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {

				String currCellFddName = kvp.getKey();
				SiteCellObj currCellObj = kvp.getValue();
				String strGnbSecCarrPrefixToUse = duInfo.map5GCellFddNameToAugIdId.get(currCellFddName);
				// GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
				boolean blnCell = (duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation && !duInfo.tmoDUInfo.duToDeltaAddCells.contains(currCellObj.cellName) && !currCellObj.getCellObj().isMovingCell()) ? false : true;
				blnCell = (duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation && duInfo.tmoDUInfo.duToDeltaAddCells.contains(currCellObj.cellName) && currCellObj.getCellObj().isMovingCell()) ? true : blnCell;
				// calculate the value of rachRootSequence to be used.
				String strRachRootSequenceToUse = "";

				try {
					strRachRootSequenceToUse = arrRachRootSeq[cellCounter + 1];
				}
				catch(Exception ex) {
					strRachRootSequenceToUse = "";
				}
				if (blnCell) {
					sb.append("pr GNBCUCPFunction=1,NRCellCU=" + currCellFddName + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,NRCellCU=" + currCellFddName + eol);
					sb.append("cellLocalId " + currCellObj.cellId + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					
					sb.append("pr GNBDUFunction=1,NRCellDU=" + currCellFddName + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBDUFunction=1,NRCellDU=" + currCellFddName + eol);
					sb.append("administrativeState 0" + eol);
					sb.append("cellLocalId " + currCellObj.cellId + eol);
					sb.append("dl256QamEnabled true" + eol);
					sb.append("nRPCI " + currCellObj.pci + eol);
					if( duInfo.isMmWave) //TMO_202
						sb.append("nRSectorCarrierRef GNBDUFunction=1,NRSectorCarrier=" + duInfo.map5GCellFddNameToAugIdId.get(currCellFddName) + "-0" + currCellFddName.charAt(currCellFddName.length()-1) + eol);
					else	
						sb.append("nRSectorCarrierRef GNBDUFunction=1,NRSectorCarrier=" + duInfo.map5GCellFddNameToAugIdId.get(currCellFddName) + "-01" + eol);
					sb.append("nRTAC " + duInfo.tac + eol);
					sb.append("pLMNIdList mcc=310,mnc=260" + eol);
					if(duInfo.isNR600 || duInfo.getSiteObj().isIs5gAnchor()) {
						if(duInfo.getSiteObj().isIs5gAnchor()) {
							sb.append("tddSpecialSlotPattern 1" + eol);
							sb.append("tddUlDlPattern 1" + eol);
						}
						sb.append("rachPreambleFormat 0" + eol);
						sb.append("rachRootSequence " + currCellObj.rachRootSequence + eol);
					} else {
						sb.append("rachRootSequence " + strRachRootSequenceToUse + eol);
					}
					sb.append("ssbDuration 1" + eol);
					sb.append("ssbFrequency 0" + eol);
					sb.append("ssbOffset 0" + eol);
					sb.append("ssbPeriodicity 20" + eol);
					if( duInfo.isMmWave) {//TMO_202
						sb.append("ssbSubCarrierSpacing 120" + eol);
						sb.append("subCarrierSpacing 120" + eol);
					}else
					if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
						sb.append("ssbSubCarrierSpacing 30" + eol);
						sb.append("subCarrierSpacing 30" + eol);
					}else {
						sb.append("ssbSubCarrierSpacing 15" + eol);
						sb.append("subCarrierSpacing 15" + eol);
					}
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("wait 5" + eol);
					sb.append(eol);
					cellCounter++;
				}
			}
			
			if(duInfo.isMmWave) //TMO_202
			{
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
		
			String currCellFddName = kvp.getKey();
			SiteCellObj currCellObj = kvp.getValue();
			String txDirection = "1";
			if(currCellFddName.endsWith("1")) 
				txDirection ="0";
			else
				txDirection ="1";
			sb.append("set NRSectorCarrier=" + duInfo.map5GCellFddNameToAugIdId.get(currCellFddName) + "-0" + currCellFddName.charAt(currCellFddName.length()-1) + " txDirection " + txDirection + eol);
				
			}
		}
			// [05042021] Removed update due to new requirement due to different parameter setting based on bands. Will be covered in NR to NR relation scripts
			/*if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q1")) {	// [04122021] TC_400 New MOs for 5G in 21.Q1
				sb.append(generateIntraFreqMCMcpcUeMCMosScript(duInfo, eol));				
			}*/

			sb.append("wait 5" + eol);
			sb.append("gs-" + eol);
			sb.append("Confbdl-" + eol);

			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generateCarrierAdd01Script exception!", ex);
			Logger.getGmoLogger().printError("Error generating CarrierAdd 01 script! " + ex.getMessage());
		}
	}

	/* Function merges logic from multiple methods to create LocalIpEndpoint with dependency on software level
	 * @param eol
	 * @param sb
	 */
	protected void generateLocalIpEndpointMo(SiteCellObj duInfo, StringBuilder sb, String router, String interfaceIPv4, String eol)
	{
		String interfaceList = (duInfo.tmoDUInfo.hasExcalibur4G5G || duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD || duInfo.has2GAnd3GSites || duInfo.has2Gsites || duInfo.has3Gsites) || CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q2") ? TMOConstants.interfaceListLocalIpEndpointAddSectorScriptLatestSWVersion : TMOConstants.interfaceListLocalIpEndpointAddSectorScriptOldSWVersion;
		interfaceList = (TMOConstants.tmoIPSecIRUConfiguration.matches("1_IRU") && duInfo.tmoDUInfo.isIPSecConfiguration)?TMOConstants.interfaceListLocalIpEndpointAddSectorScriptOldSWVersion:interfaceList;
		sb.append("pr GNBCUUPFunction=1,EndpointResource=1,LocalIpEndpoint=1" + eol);
		sb.append("if $nr_of_mos = 0" + eol);
		sb.append("crn GNBCUUPFunction=1,EndpointResource=1,LocalIpEndpoint=1" + eol);
//		sb.append("addressRef Transport=1,Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
		sb.append("addressRef Transport=1,Router=" + router + ",InterfaceIPv4=" + interfaceIPv4 + ",AddressIPv4=1" + eol);
		sb.append("interfaceList " + interfaceList + eol);
		sb.append("end" + eol);
		sb.append("fi" + eol);
		sb.append(eol);
	}

	
	/**
	 * Function to generate IntraFreqMC, IntraFreqMCCellProfile, Mcpc, McpcPCellProfile, UeMC, UeMCCellProfile MOs and NRCellCU references starting IN 21.Q1
	 * Only applicable for 5G cells, carrier add
	 * @param duInfo
	 * @param file
	 * @param eolType
	 */
	// [04122021] TC_400 New MOs for 21.Q1
	// [05042021] Removed update due to new requirement due to different parameter setting based on bands. Will be covered in NR to NR relation scripts
	/*protected StringBuilder generateIntraFreqMCMcpcUeMCMosScript(SiteCellObj duInfo, String eol) 
	{
		StringBuilder sb = new StringBuilder();
		
		try 
		{
			sb.append("//////// IntraFreqMC" + eol);
			sb.append(eol);
			sb.append("pr GNBCUCPFunction=1,IntraFreqMC=1$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn GNBCUCPFunction=1,IntraFreqMC=1" + eol);
			sb.append("intraFreqMCCellProfileUsage 1" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append("set GNBCUCPFunction=1,IntraFreqMC=1$ intraFreqMCCellProfileUsage 1" + eol);
			sb.append(eol);
			sb.append(eol);
			sb.append("//////// IntraFreqMCCellProfile" + eol);
			sb.append(eol);

			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String currCellFddName = kvp.getKey();
				SiteCellObj currCellObj = kvp.getValue();
				if (currCellObj.is5G) {
					sb.append("pr GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=" + currCellFddName + "$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=" + currCellFddName + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
			}

			sb.append(eol);
			sb.append("//////// Mcpc" + eol);
			sb.append(eol);
			sb.append("pr GNBCUCPFunction=1,Mcpc=1$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn GNBCUCPFunction=1,Mcpc=1" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			sb.append(eol);
			sb.append("//////// McpcPCellProfile - SA" + eol);
			sb.append(eol);

			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String currCellFddName = kvp.getKey();
				SiteCellObj currCellObj = kvp.getValue();
				if (currCellObj.is5G) {
					sb.append("pr GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=" + currCellFddName + "$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=" + currCellFddName + eol);
					sb.append("rsrpCriticalEnabled true" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append("set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=" + currCellFddName + "$ rsrpCriticalEnabled true" + eol);
					sb.append("set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=" + currCellFddName + "$ lowHighFreqPrioClassification 6" + eol);
					sb.append("set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=" + currCellFddName + "$ rsrpCandidateA5 threshold1 = -90,threshold2 = -93" + eol);
					sb.append("set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=" + currCellFddName + "$ rsrpCritical threshold = -121,timeToTrigger = 1280,timeToTriggerA1 = 160" + eol);
					sb.append("set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=" + currCellFddName + "$ rsrpSearchZone hysteresis = 20,threshold = -89,timeToTrigger = 640" + eol);
					sb.append(eol);
				}
			}
			
			sb.append(eol);
			sb.append("//////// UeMC" + eol);
			sb.append(eol);
			sb.append("pr GNBCUCPFunction=1,UeMC=1$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn GNBCUCPFunction=1,UeMC=1" + eol);
			sb.append("ueMCCellProfileEnabled true" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append("set GNBCUCPFunction=1,UeMC=1$ ueMCCellProfileEnabled true" + eol);
			sb.append(eol);
			sb.append(eol);
			sb.append("//////// UeMCCellProfile" + eol);
			sb.append(eol);

			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String currCellFddName = kvp.getKey();
				SiteCellObj currCellObj = kvp.getValue();
				if (currCellObj.is5G) {
					sb.append("pr GNBCUCPFunction=1,UeMC=1,UeMCCellProfile=" + currCellFddName + "$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,UeMC=1,UeMCCellProfile=" + currCellFddName + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
			}

			sb.append("//////// NRCellCU" + eol);
			sb.append(eol);

			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String currCellFddName = kvp.getKey();
				SiteCellObj currCellObj = kvp.getValue();
				if (currCellObj.is5G) {
					sb.append("pr GNBCUCPFunction=1,NRCellCU=" + currCellFddName + "$" + eol);
					sb.append("if $nr_of_mos = 1" + eol);
					sb.append("set GNBCUCPFunction=1,NRCellCU=" + currCellFddName + "$ intraFreqMCCellProfileRef IntraFreqMC=1,IntraFreqMCCellProfile=" + currCellFddName + eol);
					sb.append("set GNBCUCPFunction=1,NRCellCU=" + currCellFddName + "$ mcpcPCellEnabled true" + eol);
					sb.append("set GNBCUCPFunction=1,NRCellCU=" + currCellFddName + "$ mcpcPCellProfileRef Mcpc=1,McpcPCellProfile=" + currCellFddName + eol);
					sb.append("set GNBCUCPFunction=1,NRCellCU=" + currCellFddName + "$ ueMCCellProfileRef UeMC=1,UeMCCellProfile=" + currCellFddName + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateIntraFreqMCMcpcUeMCMosScript exception!", e);
			Logger.getGmoLogger().printError("Error generating IntraFreqMCMcpcUeMCMos Script!");
		}
		
		return sb;
	}*/

	/**
	 * Function to generateFreqRelProfilesScript
	 * @param duInfo
	 * @param file
	 * @param eolType
	 */
	// TC_400
	protected StringBuilder generateFreqRelProfilesScript(SiteCellObj duInfo) 
	{
		StringBuilder sb = new StringBuilder();

		try 
		{
			String comment = isTestServer && duInfo.tmoDUInfo.isN25MidBandScope ? "//" : "";		// [04062022] GMO_TMO-274

			// [05042021] TC_400 updated, new logic
			sb.append("func cr_IntraFreqMCCellProfile" + eol);
			sb.append("//$1 cell label" + eol);
			sb.append("//$2 endcActionEvalFail" + eol);
			sb.append("//report config A3" + eol);
			sb.append("//$3 hysteris for A3" + eol);
			sb.append("//$4 offset" + eol);
			sb.append("//$5 time to trigger" + eol);
			sb.append("//$6 Trigger quantity" + eol);
			sb.append("pr GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append(" crn GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1" + eol);

			if (!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {		// Excalibur_216
				sb.append("  betterSpCellTriggerQuantity $6" + eol);
				sb.append("  endcActionEvalFail $2" + eol);
			}
			sb.append("  rsrpBetterSCell hysteresis=10,offset=30,timeToTrigger=160" + eol);
			if (!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) 		// Excalibur_216
				sb.append("  rsrpBetterSpCell hysteresis=$3,offset=$4,timeToTrigger=$5" + eol);

			sb.append("  rsrpSCellCoverage hysteresis=10,threshold=-114,timeToTrigger=640,timeToTriggerA1=-1" + eol);
			if (!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) 		// Excalibur_216
				sb.append("  rsrqBetterSpCell hysteresis=$3,offset=$4,timeToTrigger=$5" + eol);

			sb.append("  rsrqSCellCoverage hysteresis=10,threshold=-430,timeToTrigger=640,timeToTriggerA1=-1" + eol);
			sb.append("  sCellCoverageTriggerQuantity $6" + eol);
			sb.append(" end" + eol);
			sb.append(comment + "else" + eol);
			if (!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {		// Excalibur_216
				sb.append("  set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1 betterSpCellTriggerQuantity $6" + eol);
				sb.append("  set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1 endcActionEvalFail $2" + eol);
			}
			sb.append(comment + "  set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1 rsrpBetterSCell hysteresis=10,offset=30,timeToTrigger=160" + eol);

			if (!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) // Excalibur_216
				sb.append("  set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1 rsrpBetterSpCell hysteresis=$3,offset=$4,timeToTrigger=$5" + eol);

			sb.append(comment + "  set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1 rsrpSCellCoverage hysteresis=10,threshold=-114,timeToTrigger=640,timeToTriggerA1=-1" + eol);

			if (!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) // Excalibur_216
				sb.append("  set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1 rsrqBetterSpCell hysteresis=$3,offset=$4,timeToTrigger=$5" + eol);

			sb.append(comment + "  set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1 rsrqSCellCoverage hysteresis=10,threshold=-430,timeToTrigger=640,timeToTriggerA1=-1" + eol);
			sb.append(comment + "  set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1 sCellCoverageTriggerQuantity $6" + eol);
			sb.append("fi" + eol);

			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {	// Excalibur_216
				sb.append("wait 5" + eol);
				sb.append("lt all" + eol);
				sb.append(eol);

				sb.append(comment + "set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1,IntraFreqMCCellProfileUeCfg betterSpCellTriggerQuantity $6" + eol);
				sb.append(comment + "set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1,IntraFreqMCCellProfileUeCfg endcActionEvalFail $2" + eol);
				sb.append(comment + "set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1,IntraFreqMCCellProfileUeCfg rsrpBetterSpCell hysteresis=$3,offset=$4,timeToTrigger=$5" + eol);
				sb.append(comment + "set GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$1,IntraFreqMCCellProfileUeCfg rsrqBetterSpCell hysteresis=$3,offset=$4,timeToTrigger=$5" + eol);
			}
			sb.append("endfunc" + eol);
			sb.append(eol);
			comment = "//";
			String rsrpCriticalThreshold = (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N66")) ? "-116" : "-119";
			rsrpCriticalThreshold = isTestServer && duInfo.tmoDUInfo.isN25MidBandScope && duInfo.nodeBandType.equals("N71") ? "-116" : rsrpCriticalThreshold;		// [04082022] GMO_TMO-274  
			sb.append(comment + "func cr_McpcPSCellProfile" + eol);
			sb.append("//$1 cell label" + eol);
			sb.append("//$2 hysteris for A2" + eol);
			sb.append("//$3 offset" + eol);
			sb.append("//$4 time to trigger" + eol);
			sb.append("//$5 time to trigger a1" + eol);
			if ((!(duInfo.tmoDUInfo.hasExcalibur4G5G || duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD)) && (!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q2"))) { // [07012021] GMO_TMO-101
				sb.append("pr GNBCUCPFunction=1,Mcpc=1,McpcPSCellProfile=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append(" cr GNBCUCPFunction=1,Mcpc=1,McpcPSCellProfile=1" + eol);
				sb.append("fi" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPSCellProfile=1 rsrpCritical hysteresis=10,threshold=" + rsrpCriticalThreshold + ",timeToTrigger=160,timeToTriggerA1=-1" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPSCellProfile=1 rsrpCriticalEnabled true" + eol);
			}
			else { // 21.Q2 or newer
				sb.append("pr GNBCUCPFunction=1,Mcpc=1,McpcPSCellProfile=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append(" cr GNBCUCPFunction=1,Mcpc=1,McpcPSCellProfile=1" + eol);
				sb.append("fi" + eol);
			}

			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) // Excalibur_216
			{
				sb.append("mr cellcu" + eol);
				if(duInfo.nodeBandType.equals("N71")) {
					sb.append("ma cellcu ,NRCellCU=K..........$" + eol);
				}
				else if(duInfo.nodeBandType.equals("N41")) {
					sb.append("ma cellcu ,NRCellCU=A..........$" + eol);
				}
				else {
					sb.append("ma cellcu ,NRCellCU=..........1$" + eol);
				}
				sb.append("for $mo in cellcu" + eol);
				sb.append("set $mo mcpcPSCellProfileRef Mcpc=1,McpcPSCellProfile=1" + eol);
				sb.append("done" + eol);
			}
			sb.append(comment + "endfunc" + eol);
			sb.append(eol);
			//if (duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD)
			sb.append("lt all" + eol + "wait 5" + eol); // Excalibur_216 feedback.

			comment = isTestServer && duInfo.tmoDUInfo.isN25MidBandScope ? "//" : "";		// [04062022] GMO_TMO-274
			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q2")) {
				sb.append("pr GNBCUCPFunction=1,Mcpc=1,McpcPSCellProfile=1,McpcPSCellProfileUeCfg=Base" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1,Mcpc=1,McpcPSCellProfile=1,McpcPSCellProfileUeCfg=Base" + eol);
				sb.append("lowHighFreqPrioClassification 7" + eol);
				sb.append("mcpcQuantityList 0" + eol);
				sb.append("rsrpCandidateA5 hysteresis=10,threshold1=-156,threshold2=-156,timeToTrigger=640" + eol);
				sb.append("rsrpCritical hysteresis=10,threshold=" + rsrpCriticalThreshold + ",timeToTrigger=160" + eol);
				sb.append("rsrpCriticalEnabled true" + eol);
				sb.append("rsrpSearchTimeRestriction -1" + eol);
				sb.append("rsrpSearchZone hysteresis=10,threshold=-156,timeToTrigger=160,timeToTriggerA1=-1" + eol);
				sb.append("userLabel" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append(comment + "set GNBCUCPFunction=1,Mcpc=1,McpcPSCellProfile=1,McpcPSCellProfileUeCfg=Base rsrpCritical hysteresis=10,threshold=" + rsrpCriticalThreshold + ",timeToTrigger=160" + eol);
				sb.append(comment + "set GNBCUCPFunction=1,Mcpc=1,McpcPSCellProfile=1,McpcPSCellProfileUeCfg=Base rsrpCriticalEnabled true" + eol);
				sb.append(eol);
			}

			sb.append("func cr_mcpcpcellprofile" + eol);
			sb.append("//$1 cellname profile name" + eol);
			sb.append("//$2 source cell Freq Relation for ARFCN CellResel priority for setting lowHighFreqPrioClassification" + eol);
			sb.append("//$3 cell band" + eol);
			sb.append("// TMO Design values for N71 and N41 were used" + eol);
			sb.append("//N71, the" + eol);
			sb.append(eol);
			sb.append("pr GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1" + eol);
			sb.append("$create = 0" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append(" $create = 1" + eol);
			sb.append("fi" + eol);
			sb.append("if $create = 1" + eol);
			sb.append(" cr GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1" + eol);
			sb.append("fi" + eol);
			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) 	{	// Excalibur_216
				sb.append("wait 5" + eol);
				sb.append("lt all" + eol);
			}
			if ((duInfo.tmoDUInfo.hasExcalibur4G5G || duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD) || CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q2")) { // [07082021] GMO_TMO-101 less bands for 5G in 21.Q2
				sb.append(comment + "if $3 = 71" + eol);
				if (/*isTestServer && */CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "22.Q1"))	{	// GMO_TMO-304 BAU and Excal
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base lowHighFreqPrioClassification 5" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateA5 hysteresis=10,threshold1=-115,threshold2=-113,timeToTrigger=640" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateB2 hysteresis=10,threshold1=-115,threshold2EUtra=-125,timeToTrigger=320" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCritical hysteresis=10,threshold=-117,timeToTrigger=640,timeToTriggerA1=640" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCriticalEnabled true" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchTimeRestriction -1" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchZone hysteresis=20,threshold=-80,timeToTrigger=640,timeToTriggerA1=320" + eol);
				}
				else if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4"))	{	// Excalibur_216
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base lowHighFreqPrioClassification 5" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateA5 hysteresis=10,threshold1=-116,threshold2=-113,timeToTrigger=640" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateB2 hysteresis=10,threshold1=-116,threshold2EUtra=-124,timeToTrigger=640" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCritical hysteresis=10,threshold=-124,timeToTrigger=1280,timeToTriggerA1=640" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCriticalEnabled true" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchTimeRestriction -1" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchZone hysteresis=20,threshold=-89,timeToTrigger=320,timeToTriggerA1=320" + eol);
				}
				else {
					sb.append(comment + "  set McpcPCellProfile lowHighFreqPrioClassification 5" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpCandidateA5 hysteresis=10,threshold1=-116,threshold2=-113,timeToTrigger=640" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpCandidateB2 hysteresis=10,threshold1=-116,threshold2EUtra=-124,timeToTrigger=640" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpCritical hysteresis=10,threshold=-124,timeToTrigger=1280,timeToTriggerA1=640" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpCriticalEnabled true" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpSearchTimeRestriction -1" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpSearchZone hysteresis=20,threshold=-89,timeToTrigger=320,timeToTriggerA1=320" + eol);
				}
				sb.append(eol);
				sb.append(comment + "else if $3 = 41" + eol);
				if (/*isTestServer && */CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "22.Q1"))	{	// GMO_TMO-304 BAU and Excal
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base lowHighFreqPrioClassification 5" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateA5 hysteresis=10,threshold1=-106,threshold2=-113,timeToTrigger=320" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateB2 hysteresis=10,threshold1=-109,threshold2EUtra=-124,timeToTrigger=320" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCritical hysteresis=10,threshold=-111,timeToTrigger=640,timeToTriggerA1=640" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCriticalEnabled true" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchTimeRestriction -1" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchZone hysteresis=20,threshold=-113,timeToTrigger=320,timeToTriggerA1=320" + eol);
				}
				else if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4"))	{	// Excalibur_216
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base lowHighFreqPrioClassification 5" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateA5 hysteresis=10,threshold1=-102,threshold2=-113,timeToTrigger=640" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateB2 hysteresis=10,threshold1=-116,threshold2EUtra=-124,timeToTrigger=640" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCritical hysteresis=10,threshold=-109,timeToTrigger=1280,timeToTriggerA1=640" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCriticalEnabled true" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchTimeRestriction -1" + eol);
					sb.append(comment + "  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchZone hysteresis=20,threshold=-101,timeToTrigger=320,timeToTriggerA1=320" + eol);
				}
				else {
					sb.append(comment + "  set McpcPCellProfile lowHighFreqPrioClassification 5" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpCandidateA5 hysteresis=10,threshold1=-102,threshold2=-113,timeToTrigger=640" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpCandidateB2 hysteresis=10,threshold1=-116,threshold2EUtra=-124,timeToTrigger=640" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpCritical hysteresis=10,threshold=-109,timeToTrigger=1280,timeToTriggerA1=640" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpCriticalEnabled true" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpSearchTimeRestriction -1" + eol);
					sb.append(comment + "  set McpcPCellProfile rsrpSearchZone hysteresis=20,threshold=-101,timeToTrigger=320,timeToTriggerA1=320" + eol);
				}
				if (!comment.isEmpty()) {		// [04082022] GMO_TMO-274
					sb.append(eol);
					sb.append(comment + "if $3 = 25" + eol);
					if (/*isTestServer && */CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "22.Q1"))	{	// GMO_TMO-304 BAU and Excal
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base lowHighFreqPrioClassification 5" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateA5 hysteresis=10,threshold1=-106,threshold2=-113,timeToTrigger=320" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateB2 hysteresis=10,threshold1=-109,threshold2EUtra=-124,timeToTrigger=320" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCritical hysteresis=10,threshold=-111,timeToTrigger=640,timeToTriggerA1=640" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCriticalEnabled true" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchTimeRestriction -1" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchZone hysteresis=20,threshold=-113,timeToTrigger=320,timeToTriggerA1=320" + eol);
					}
					else if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4"))	{	// Excalibur_216
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base lowHighFreqPrioClassification 5" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateA5 hysteresis=10,threshold1=-102,threshold2=-113,timeToTrigger=640" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCandidateB2 hysteresis=10,threshold1=-116,threshold2EUtra=-124,timeToTrigger=640" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCritical hysteresis=10,threshold=-109,timeToTrigger=1280,timeToTriggerA1=640" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpCriticalEnabled true" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchTimeRestriction -1" + eol);
						sb.append("  set McpcPCellProfile=$1,McpcPCellProfileUeCfg=Base rsrpSearchZone hysteresis=20,threshold=-101,timeToTrigger=320,timeToTriggerA1=320" + eol);
					}
				}
				sb.append("fi" + eol);
			}
			else {			// TODO delete pre 21.Q2?
				sb.append("if $3 = 71" + eol);
				sb.append("   set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 lowHighFreqPrioClassification $2" + eol);
				sb.append("   set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 mcpcQuantityList 0" + eol);
				sb.append("   set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCandidateA5 hysteresis=10,threshold1=-90,threshold2=-101,timeToTrigger=640" + eol);
				sb.append("   set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCandidateB2 hysteresis=10,threshold1=-116,threshold2EUtra=-124,timeToTrigger=640" + eol);
				sb.append("   set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCritical hysteresis=10,threshold=-119,timeToTrigger=1280,timeToTriggerA1=640" + eol);
				sb.append("   set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCriticalEnabled true" + eol);
				sb.append("   set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpSearchTimeRestriction -1" + eol);
				sb.append("   set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpSearchZone hysteresis=20,threshold=-89,timeToTrigger=320,timeToTriggerA1=320" + eol);
				sb.append("else if $3 = 41" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 lowHighFreqPrioClassification $2" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 mcpcQuantityList 0" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCandidateA5 hysteresis=10,threshold1=-102,threshold2=-121,timeToTrigger=640" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCandidateB2 hysteresis=10,threshold1=-102,threshold2EUtra=-124,timeToTrigger=640" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCritical hysteresis=10,threshold=-104,timeToTrigger=1280,timeToTriggerA1=640" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCriticalEnabled true" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpSearchTimeRestriction -1" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpSearchZone hysteresis=20,threshold=-101,timeToTrigger=320,timeToTriggerA1=320" + eol);
				sb.append("else if $3 = 66" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 lowHighFreqPrioClassification $2" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 mcpcQuantityList 0" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCandidateA5 hysteresis=10,threshold1=-115,threshold2=-121,timeToTrigger=640" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCandidateB2 hysteresis=10,threshold1=-118,threshold2EUtra=-124,timeToTrigger=640" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCritical hysteresis=10,threshold=-121,timeToTrigger=1280,timeToTriggerA1=640" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCriticalEnabled true" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpSearchTimeRestriction -1" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpSearchZone hysteresis=20,threshold=-114,timeToTrigger=320,timeToTriggerA1=320" + eol);
				sb.append("else if $3 = 2" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 lowHighFreqPrioClassification $2" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 mcpcQuantityList 0" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCandidateA5 hysteresis=10,threshold1=-115,threshold2=-121,timeToTrigger=640" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCandidateB2 hysteresis=10,threshold1=-118,threshold2EUtra=-124,timeToTrigger=640" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCritical hysteresis=10,threshold=-121,timeToTrigger=1280,timeToTriggerA1=640" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpCriticalEnabled true" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpSearchTimeRestriction -1" + eol);
				sb.append("  set GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$1 rsrpSearchZone hysteresis=20,threshold=-114,timeToTrigger=320,timeToTriggerA1=320" + eol);
				sb.append("fi" + eol);
			}
			sb.append("endfunc" + eol);
			sb.append(eol);
			sb.append("func cr_UeMCCellProfile" + eol);
			sb.append("//$1 Cellname label" + eol);
			if (!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {	// Excalibur_216
				sb.append("//$2 filterCoefficientNrRsrpLow" + eol);
				sb.append("//$3 filterCoefficientNrRsrqLow" + eol);
			}
			sb.append(" pr GNBCUCPFunction=1,UeMC=1,UeMCCellProfile=$1" + eol);
			sb.append(" if $nr_of_mos = 0" + eol);
			sb.append("  cr GNBCUCPFunction=1,UeMC=1,UeMCCellProfile=$1" + eol);
			sb.append(" fi" + eol);
			// [05252021 - ezrxxsu] - Removed below lines per request from Ada
			// sb.append(" set GNBCUCPFunction=1,UeMC=1,UeMCCellProfile=$1 filterCoefficientNrRsrpLow $2" + eol);
			// sb.append(" set GNBCUCPFunction=1,UeMC=1,UeMCCellProfile=$1 filterCoefficientNrRsrqLow $3" + eol);
			sb.append("endfunc" + eol);
			sb.append(eol);
			sb.append("func cr_McpcPCellNrFreqRelProfile" + eol);
			sb.append("//$1 Freq ARFCN label" + eol);
			sb.append(" pr GNBCUCPFunction=1,Mcpc=1,McpcPCellNrFreqRelProfile=$1$" + eol);
			sb.append(" if $nr_of_mos = 0" + eol);
			sb.append("  crn GNBCUCPFunction=1,Mcpc=1,McpcPCellNrFreqRelProfile=$1" + eol);
			if (!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {	// Excalibur_216
				sb.append("   inhibitMeasForCellCandidate false" + eol);
				sb.append("   rsrpCandidateA5Offsets threshold1Offset=0,threshold2Offset=0" + eol);
			}
			sb.append("  end" + eol);
			sb.append(" fi" + eol);
			sb.append("endfunc" + eol);
			sb.append(eol);
			//[ezrxxsu - 01272022]
			sb.append("func cr_McpcPSCellNrFreqRelProfile" + eol);
			sb.append("pr GNBCUCPFunction=1,Mcpc=1,McpcPSCellNrFreqRelProfile=$1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn GNBCUCPFunction=1,Mcpc=1,McpcPSCellNrFreqRelProfile=$1" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			if(duInfo.nodeBandType.equals("N71")) {
				sb.append("set GNBCUCPFunction=1,NRCellCU=K.*,NRFreqRelation=$1 mcpcPSCellNrFreqRelProfileRef Mcpc=1,McpcPSCellNrFreqRelProfile=$1" + eol);
			}
			else if(duInfo.nodeBandType.equals("N41")){
				sb.append("set GNBCUCPFunction=1,NRCellCU=A.*,NRFreqRelation=$1 mcpcPSCellNrFreqRelProfileRef Mcpc=1,McpcPSCellNrFreqRelProfile=$1" + eol);
			}
			else {
				sb.append("set GNBCUCPFunction=1,NRCellCU=.*,NRFreqRelation=$1 mcpcPSCellNrFreqRelProfileRef Mcpc=1,McpcPSCellNrFreqRelProfile=$1" + eol);
			}
			sb.append("endfunc" + eol);
			sb.append(eol);
			sb.append("func cr_UeMCNrFreqRelProfile" + eol);
			sb.append("//$1 Freq ARFCN Label" + eol);
			sb.append("//$2 connModePrioPCell" + eol);
			sb.append(" pr GNBCUCPFunction=1,UeMC=1,UeMCNrFreqRelProfile=$nrfreqval$" + eol);
			sb.append(" if $nr_of_mos = 0" + eol);
			sb.append("  crn GNBCUCPFunction=1,UeMC=1,UeMCNrFreqRelProfile=$1" + eol);
			if (!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {	// Excalibur_216
				sb.append("   connModeAllowedPCell true" + eol);
				sb.append("   connModePrioPCell $2" + eol);
			}
			sb.append("   userLabel" + eol);
			sb.append("  end" + eol);
			sb.append(" fi" + eol);
			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {	// Excalibur_216
				sb.append("wait 5" + eol);
				sb.append("lt all" + eol);
			}

			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {	// Excalibur_216
				sb.append(" set GNBCUCPFunction=1,UeMC=1,UeMCNrFreqRelProfile=$1,UeMCNrFreqRelProfileUeCfg connModeAllowedPCell true" + eol);
				sb.append(" set GNBCUCPFunction=1,UeMC=1,UeMCNrFreqRelProfile=$1,UeMCNrFreqRelProfileUeCfg connModePrioPCell $2" + eol);
			}
			else {
				sb.append(" set GNBCUCPFunction=1,UeMC=1,UeMCNrFreqRelProfile=$1 connModeAllowedPCell true" + eol);
				sb.append(" set GNBCUCPFunction=1,UeMC=1,UeMCNrFreqRelProfile=$1 connModePrioPCell $2" + eol);
			}
			sb.append("endfunc" + eol);
			sb.append(eol);
			sb.append("//Build the HighLevel MO's" + eol);
			sb.append("//" + eol);
			sb.append("//Build new UE Mobility Control Main MO's" + eol);
			sb.append("pr GNBCUCPFunction=1,IntraFreqMC=1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append(" cr GNBCUCPFunction=1,IntraFreqMC=1" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			sb.append("//set intraFreqMCCellProfileUsage to 1 (COMPLETE_USAGE)" + eol);
			sb.append("//set intraFreqMCCellProfileUsage to 0 (LIMITED_USAGE), ReportConfigA3 will still be used." + eol);
			sb.append("set GNBCUCPFunction=1,IntraFreqMC=1 intraFreqMCCellProfileUsage 1" + eol);
			sb.append(eol);
			sb.append("pr GNBCUCPFunction=1,Mcpc=1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append(" cr GNBCUCPFunction=1,Mcpc=1" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			sb.append("pr GNBCUCPFunction=1,UeMc=1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append(" cr GNBCUCPFunction=1,UeMc=1" + eol);
			sb.append("fi" + eol);
			sb.append("//set ueMCCellProfileEnabled to enabled" + eol);
			sb.append("//set GNBCUCPFunction=1,UeMc=1 ueMCCellProfileEnabled true" + eol);
			sb.append("//setting to false will cause the UeMeasControl parameters to be used." + eol);
			sb.append("set GNBCUCPFunction=1,UeMc=1 ueMCCellProfileEnabled true" + eol);
			sb.append(eol);
			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) // Excalibur_216
				sb.append("mr celldugrp" + eol);
			sb.append(eol);
			if(duInfo.nodeBandType.equals("N71")) {
				sb.append("ma celldugrp ,NRCellDU=K.*$ administrativeState 1" + eol);
			}
			else if(duInfo.nodeBandType.equals("N41")) {
				sb.append("ma celldugrp ,NRCellDU=A.*$ administrativeState 1" + eol);
			}
			else {
				sb.append("ma celldugrp ,NRCellDU=.*1$ administrativeState 1" + eol);
			}
			sb.append("bl celldugrp" + eol);
			sb.append("wait 10" + eol);
			sb.append(eol);
			sb.append("//copy the reportconfigA3 to IntraFreqMCCellProfile" + eol);
			sb.append("//copy the reportconfigA2 -> mcpcPSCellProfile for endc NR -> LTE session cont." + eol);
			sb.append("mr cellcu" + eol);
			if(duInfo.nodeBandType.equals("N71")) {
				sb.append("ma cellcu ,NRCellCU=K..........$" + eol);
			}
			else if(duInfo.nodeBandType.equals("N41")) {
				sb.append("ma cellcu ,NRCellCU=A..........$" + eol);
			}
			else {
				sb.append("ma cellcu ,NRCellCU=..........1$" + eol);
			}
			sb.append("// get current values from reportconfiga2 and reportconfiga3 to build the new MO's IntraFreqMCCellProfile" + eol);
			sb.append("for $mo in cellcu" + eol);
			sb.append(" get $mo nRCellCUId > $cellname" + eol);
			sb.append(" $cellldn = ldn($mo)" + eol);
			sb.append(" $reporta3 = $cellldn,UeMeasControl=1,ReportConfigA3=1" + eol);
			sb.append(" $reporta3pr = proxy($reporta3)" + eol);
			sb.append(" //pr $reporta3pr" + eol);
			sb.append(" get $reporta3pr endcActionA3EvalFail" + eol);
			sb.append(" if $nr_of_mos = 1" + eol);
			sb.append("  get $reporta3pr endcActionA3EvalFail > $endcact" + eol);
			sb.append("  $endcactarr = split($endcact)" + eol);
			sb.append("  $endcactevalfail = $endcactarr[1]" + eol);
			sb.append("  get $reporta3pr hysteresis > $hyst" + eol);
			sb.append("  get $reporta3pr offset > $a3offset" + eol);
			sb.append("  get $reporta3pr timeToTrigger > $a3ttt" + eol);
			sb.append("  get $reporta3pr triggerQuantity > $triggert" + eol);
			sb.append("  $triggertarr = split($triggert)" + eol);
			sb.append("  $triggertypea3 = $triggertarr[1]" + eol);
			sb.append(" else" + eol);
			sb.append("  $endcactevalfail = 0" + eol);
			sb.append("  $hyst = 10" + eol);
			sb.append("  $a3offset = 30" + eol);
			sb.append("  $a3ttt = 640" + eol);
			sb.append("  $triggertypea3 = 0" + eol);
			sb.append("  //cr_IntraFreqMCCellProfile $cellname 0 10 30 640 0" + eol);
			sb.append(" fi" + eol);
			sb.append(" cr_IntraFreqMCCellProfile $cellname $endcactevalfail $hyst $a3offset $a3ttt $triggertypea3" + eol);
			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) // Excalibur_216
				sb.append(" set $cellldn intraFreqMCCellProfileRef GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$cellname" + eol);
			else
				sb.append(" set $mo intraFreqMCCellProfileRef GNBCUCPFunction=1,IntraFreqMC=1,IntraFreqMCCellProfile=$cellname" + eol);
			sb.append("done" + eol);
			sb.append(eol);
			sb.append("deb celldugrp" + eol);
			sb.append("wait 10" + eol);
			sb.append(eol);
			sb.append("func cr_freqRelprofiles" + eol);
			sb.append("//$1 cellband" + eol);
			sb.append("//$2 cellname" + eol);
			sb.append("$cellband = $1" + eol);
			sb.append("$cellname = $2" + eol);
			sb.append("mr nrfreqrel" + eol);
			sb.append("ma nrfreqrel GNBCUCPFunction=1,NRCellCU=$cellname,NRFreqRelation=" + eol);
			sb.append("for $mo in nrfreqrel" + eol);
			sb.append(" //get $mo nRFreqRelationId > $nrfreqval" + eol);
			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) // Excalibur_216
				sb.append(" $cellldn1 = ldn($mo)" + eol);
			sb.append(" get $mo nRFrequencyRef > $nrfreqref" + eol);
			sb.append(" $nrfreqrefpr = proxy($nrfreqref)" + eol);
			sb.append(" get $nrfreqrefpr arfcnValueNRDl > $nrfreqval" + eol);
			sb.append(" get $nrfreqrefpr ^bandList$ > $nrfreqbandstr" + eol);
			sb.append(" $freqband = 0" + eol);
			sb.append(comment + " if $nrfreqbandstr ~ 71" + eol);
			sb.append(comment + "  $freqband = 71" + eol);
			sb.append(comment + " else if  $nrfreqbandstr ~ 41" + eol);
			sb.append(comment + "  $freqband = 41" + eol);
			sb.append(comment + " else if  $nrfreqbandstr ~ 66" + eol);
			sb.append(comment + "  $freqband = 66" + eol);
			sb.append(comment + " else if  $nrfreqbandstr ~ 2" + eol);
			sb.append(comment + "  $freqband = 2" + eol);
			if (!comment.isEmpty()) {			// [04062022] GMO_TMO-274
				sb.append(" if $nrfreqbandstr ~ 25" + eol);
				sb.append("  $freqband = 25" + eol);
			}
			sb.append(" fi" + eol);
			sb.append(" unset nrfreqbandstr" + eol);
			sb.append(" $crsp = 0" + eol);
			sb.append(comment + " if $cellband = 71 && $freqband = 41" + eol);
			sb.append(comment + "  $crsp = 6" + eol);
			sb.append(comment + " else if $cellband = 71 && $freqband = 66" + eol);
			sb.append(comment + "  $crsp = 5" + eol);
			sb.append(comment + " else if $cellband = 71 && $freqband = 2" + eol);
			sb.append(comment + "  $crsp = 5" + eol);
			if (!comment.isEmpty()) {			// [04062022] GMO_TMO-274
				sb.append(" if $cellband = 71 && $freqband = 25" + eol);
				sb.append("  $crsp = 5" + eol);
			}
			sb.append(comment + " else if $cellband = 71 && $freqband = 71" + eol);
			sb.append(comment + "  $crsp = 7" + eol);
			sb.append(" fi" + eol);
			sb.append(comment + " if $cellband = 41 && $freqband = 71" + eol);
			sb.append(comment + "  $crsp = 6" + eol);
			sb.append(comment + " else if $cellband = 41 && $freqband = 66" + eol);
			sb.append(comment + "  $crsp = 5" + eol);
			sb.append(comment + " else if $cellband = 41 && $freqband = 2" + eol);
			sb.append(comment + "  $crsp = 5" + eol);
			if (!comment.isEmpty()) {			// [04062022] GMO_TMO-274
				sb.append(" if $cellband = 41 && $freqband = 25" + eol);
				sb.append("  $crsp = 5" + eol);
			}
			sb.append(comment + " else if $cellband = 41 && $freqband = 41" + eol);
			sb.append(comment + "  $crsp = 7" + eol);
			sb.append(" fi" + eol);
			sb.append(comment + " if $cellband = 66 && $freqband = 71" + eol);
			sb.append(comment + "  $crsp = 5" + eol);
			sb.append(comment + " else if $cellband = 66 && $freqband = 41" + eol);
			sb.append(comment + "  $crsp = 6" + eol);
			sb.append(comment + " else if $cellband = 66 && $freqband = 2" + eol);
			sb.append(comment + "  $crsp = 5" + eol);
			sb.append(comment + " else if $cellband = 66 && $freqband = 66" + eol);
			sb.append(comment + "  $crsp = 7" + eol);
			sb.append(comment + " fi" + eol);
			if (!comment.isEmpty()) {			// [04062022] GMO_TMO-274
				sb.append(" if $cellband = 25 && $freqband = 71" + eol);
				sb.append("  $crsp = 5" + eol);
				sb.append(" else if $cellband = 25 && $freqband = 41" + eol);
				sb.append("  $crsp = 6" + eol);
				sb.append("// else if $cellband = 25 && $freqband = 66" + eol);
				sb.append("//  $crsp = 5" + eol);
				sb.append("// else if $cellband = 25 && $freqband = 25" + eol);
				sb.append("//  $crsp = 7" + eol);
				sb.append(" fi" + eol);
			}
			sb.append(comment + " if $cellband = 2 && $freqband = 71" + eol);
			sb.append(comment + "  $crsp = 5" + eol);
			sb.append(comment + " else if $cellband = 2 && $freqband = 41" + eol);
			sb.append(comment + "  $crsp = 6" + eol);
			sb.append(comment + " else if $cellband = 2 && $freqband = 66" + eol);
			sb.append(comment + "  $crsp = 5" + eol);
			sb.append(comment + " else if $cellband = 2 && $freqband = 2" + eol);
			sb.append(comment + "  $crsp = 7" + eol);
			sb.append(comment + " fi" + eol);
			sb.append(" //pr GNBCUCPFunction=1,UeMC=1,UeMCNrFreqRelProfile=$nrfreqval$" + eol);
			sb.append(" //if $nr_of_mos = 0" + eol);
			sb.append(" cr_UeMCNrFreqRelProfile $nrfreqval $crsp" + eol);
			sb.append(" //fi" + eol);
			sb.append(" //pr GNBCUCPFunction=1,Mcpc=1,McpcPCellNrFreqRelProfile=$nrfreqval$" + eol);
			sb.append(" //if $nr_of_mos = 0" + eol);
			sb.append(" cr_McpcPCellNrFreqRelProfile $nrfreqval" + eol);
			sb.append(" cr_McpcPSCellNrFreqRelProfile $nrfreqval" + eol);
			sb.append(" //fi" + eol);
			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {	// Excalibur_216
				sb.append("  set $cellldn1 ueMCNrFreqRelProfileRef GNBCUCPFunction=1,UeMC=1,UeMCNrFreqRelProfile=$nrfreqval" + eol);
				sb.append("  set $cellldn1 mcpcPCellNrFreqRelProfileRef GNBCUCPFunction=1,Mcpc=1,McpcPCellNrFreqRelProfile=$nrfreqval" + eol);
			}
			else {
				sb.append(" set $mo ueMCNrFreqRelProfileRef GNBCUCPFunction=1,UeMC=1,UeMCNrFreqRelProfile=$nrfreqval" + eol);
				sb.append(" set $mo mcpcPCellNrFreqRelProfileRef GNBCUCPFunction=1,Mcpc=1,McpcPCellNrFreqRelProfile=$nrfreqval" + eol);
			}
			sb.append("done" + eol);
			sb.append("endfunc" + eol);
			sb.append(eol);
			sb.append("mr celldu" + eol);
			if(duInfo.nodeBandType.equals("N71")) {
				sb.append("ma celldu ,NRCellDU=K.........1$" + eol);
			}
			else if(duInfo.nodeBandType.equals("N41")) {
				sb.append("ma celldu ,NRCellDU=A.........1$" + eol);
			}
			else {
				sb.append("ma celldu ,NRCellDU=..........1$" + eol);
			}
			sb.append(eol);
			sb.append("//Build MO UeMCNrFreqRelProfile and McpcPCellNrFreqRelProfile for the NR FreqRelations currently configured." + eol);
			sb.append("for $mo in celldu" + eol);
			sb.append(" get $mo ^nRCellDUId$ > $cellname" + eol);
			sb.append(" //get $mo ^bandList$ > $cellbandstr" + eol);
			sb.append(" $nrcellcustr = GNBCUCPFunction=1,NRCellCU=$cellname" + eol);
			sb.append(" $nrcellcu_pr = proxy($nrcellcustr)" + eol);
			sb.append(" get $nrcellcu_pr nRFrequencyRef > $freqref" + eol);
			sb.append(" get $freqref ^bandList$ > $cellbandstr" + eol);
			sb.append(" $cellband = 0" + eol);
			sb.append(comment + " if $cellbandstr ~ 71" + eol);
			sb.append(comment + "  $cellband = 71" + eol);
			sb.append(comment + " else if  $cellbandstr ~ 41" + eol);
			sb.append(comment + "  $cellband = 41" + eol);
			sb.append(comment + " else if  $cellbandstr ~ 66" + eol);
			sb.append(comment + "  $cellband = 66" + eol);
			sb.append(comment + " else if  $cellbandstr ~ 2" + eol);
			sb.append(comment + "  $cellband = 2" + eol);
			if (!comment.isEmpty()) {			// [04062022] GMO_TMO-274
				sb.append(" if  $cellbandstr ~ 25" + eol);
				sb.append("  $cellband = 25" + eol);
			}
			sb.append(" fi" + eol);
			sb.append(" if $cellband > 0" + eol);
			sb.append("  cr_freqRelprofiles $cellband $cellname" + eol);
			sb.append(" else" + eol);
			sb.append("  l echo \"could not determine Cell-Band for $nodename, $cellname\"" + eol);
			sb.append(" fi" + eol);
			sb.append(" unset $cellbandstr" + eol);
			sb.append(" unset $cellband" + eol);
			sb.append(" unset $cellname" + eol);
			sb.append(" unset $nrcellcustr" + eol);
			sb.append(" unset $nrcellcu_pr" + eol);
			sb.append(" unset $freqref" + eol);
			sb.append("done" + eol);
			sb.append(eol);
			sb.append("//lock NRCellDU" + eol);
			sb.append("bl celldugrp" + eol);
			sb.append("wait 10" + eol);
			sb.append("mr cellcu" + eol);
			if(duInfo.nodeBandType.equals("N71")) {
				sb.append("ma cellcu ,NRCellCU=K..........$" + eol);
			}
			else if(duInfo.nodeBandType.equals("N41")) {
				sb.append("ma cellcu ,NRCellCU=A..........$" + eol);
			}
			else {
				sb.append("ma cellcu ,NRCellCU=..........1$" + eol);
			}
			sb.append(eol);
			sb.append("for $mo in cellcu" + eol);
			sb.append(" get $mo nRCellCUId > $cellname" + eol);
			sb.append(" $cellldn = ldn($mo)" + eol);
			sb.append(" get $mo nRFrequencyRef > $freqref" + eol);
			sb.append(" get $freqref ^bandList$ > $cellbandstr" + eol);
			sb.append(" $cellband = 0" + eol);
			sb.append(comment + " if $cellbandstr ~ 71" + eol);
			sb.append(comment + "  $cellband = 71" + eol);
			sb.append(comment + " else if  $cellbandstr ~ 41" + eol);
			sb.append(comment + "  $cellband = 41" + eol);
			sb.append(comment + " else if  $cellbandstr ~ 66" + eol);
			sb.append(comment + "  $cellband = 66" + eol);
			sb.append(comment + " else if  $cellbandstr ~ 2" + eol);
			sb.append(comment + "  $cellband = 2" + eol);
			if (!comment.isEmpty()) {			// [04062022] GMO_TMO-274
				sb.append(" if  $cellbandstr ~ 25" + eol);
				sb.append("  $cellband = 25" + eol);
			}
			sb.append(" fi" + eol);
			sb.append(" unset $cellbandstr" + eol);
			sb.append(" get $freqref arfcnValueNRDl > $freqarfcnval" + eol);
			sb.append(" $freqrelstr = $cellldn,NRFreqRelation=$freqarfcnval" + eol);
			sb.append(" $freqrelpr = proxy($freqrelstr)" + eol);
			sb.append(" get $freqrelpr ^cellReselectionPriority$ > $freqprio" + eol);
			sb.append(" // TMO Configuration of lowHighFreqPrioClassification value of 6 for both N41 and N71 cells" + eol);
			sb.append(" //if $nr_of_mos = 0" + eol);
			sb.append("  $freqprio = 6" + eol);
			sb.append(" //fi" + eol);
			sb.append(" pr GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$cellname$" + eol);
			sb.append(" if $cellband > 0" + eol);
			sb.append("  //cr GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$cellname" + eol);
			sb.append("  cr_mcpcpcellprofile $cellname $freqprio $cellband" + eol);
			sb.append(" fi" + eol);
			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {	// Excalibur_216
				sb.append("// get $cellldn,UeMeasControl=1 filterCoefficientNrRsrp > $cellfcnrrsrp" + eol);
				sb.append("// get $cellldn,UeMeasControl=1 filterCoefficientNrRsrq > $cellfcnrrsrq" + eol);
				sb.append(eol);
				sb.append("// get $cellldn,UeMeasControl=1 sMeasure > $cellfcnrsmeas" + eol);
			}
			else {
				sb.append(" get $cellldn,UeMeasControl=1 filterCoefficientNrRsrp > $cellfcnrrsrp" + eol);
				sb.append(" get $cellldn,UeMeasControl=1 filterCoefficientNrRsrq > $cellfcnrrsrq" + eol);
				sb.append(eol);
				sb.append(" get $cellldn,UeMeasControl=1 sMeasure > $cellfcnrsmeas" + eol);
			}
			sb.append(" pr GNBCUCPFunction=1,UeMC=1,UeMCCellProfile=$cellname$" + eol);
			sb.append(" if $cellband > 0" + eol);
			sb.append("  //cr GNBCUCPFunction=1,UeMC=1,UeMCCellProfile=$cellname" + eol);
			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) // Excalibur_216
				sb.append("  cr_UeMCCellProfile $cellname" + eol);
			else
				sb.append("  cr_UeMCCellProfile $cellname $cellfcnrrsrp $cellfcnrrsrq" + eol);
			sb.append("  //set sMeasure value to default value of -29, based on PDU recommendation." + eol);
			sb.append("  //set GNBCUCPFunction=1,UeMC=1,UeMCCellProfile=$cellname sMeasure $cellfcnrsmeas" + eol);
			sb.append(" fi" + eol);
			sb.append(" if $cellband > 0" + eol);
			if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {	// Excalibur_216
				sb.append("  set $cellldn mcpcPCellProfileRef GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$cellname" + eol);
				sb.append("  set $cellldn ueMCCellProfileRef GNBCUCPFunction=1,UeMC=1,UeMCCellProfile=$cellname" + eol);
			}
			else {
				sb.append("  set $mo mcpcPCellProfileRef GNBCUCPFunction=1,Mcpc=1,McpcPCellProfile=$cellname" + eol);
				sb.append("  set $mo ueMCCellProfileRef GNBCUCPFunction=1,UeMC=1,UeMCCellProfile=$cellname" + eol);
			}
			sb.append("  //disable mcpc to ensure that the legacy MO's are still in play" + eol);
			sb.append("  //for enabling MCPC configuration set to true" + eol);
			if (/*isTestServer && */CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "22.Q1"))	{	// GMO_TMO-304 BAU and Excal
				sb.append("  set $cellldn mcpcPCellEnabled true" + eol);
				sb.append("  //set $cellldn mcpcPCellEnabled false" + eol);
			}
			else if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q4")) {	// Excalibur_216
				sb.append("  //set $cellldn mcpcPCellEnabled true" + eol);
				sb.append("  set $cellldn mcpcPCellEnabled false" + eol);
			}
			else {
				sb.append("  //set $mo mcpcPCellEnabled true" + eol);
				sb.append("  set $mo mcpcPCellEnabled false" + eol);
			}
			sb.append(" fi" + eol);
			sb.append(" unset $freqref" + eol);
			sb.append(" unset $freqrelstr" + eol);
			sb.append(" unset $freqrelpr" + eol);
			sb.append(" unset $freqarfcnval" + eol);
			sb.append(" unset $freqprio" + eol);
			sb.append("done" + eol);
			sb.append(eol);

			if((!duInfo.tmoDUInfo.isExcalibur4G5GFDD && !duInfo.tmoDUInfo.isExcalibur4G5GTDD && !CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q2"))) {
				sb.append("deb celldugrp" + eol);
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateFreqRelProfilesScript exception!", e);
			Logger.getGmoLogger().printError("Error generating FreqRelProfiles Script!");
		}
		
		return sb;
	}
	
	/**
	 * This function is generate Mobility Parameter Change Script for NR Node where NR-NR Relation script will not generated
	 * @param duInfo
	 * @param file
	 * @param eolType
	 * @return
	 */
	protected void generateMobilityParameterChangeScript(SiteCellObj duInfo, String file, String eolType) {
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();
		try {
			sb.append(genericScriptBlockGenerator.generateConfbdlPlusGenericBlock());
			sb.append(generateFreqRelProfilesScript(duInfo));
			tmoCCR.generateGnbcucGnbduNewChildMos(duInfo, sb);
			sb.append(genericScriptBlockGenerator.generateConfbdlMinusGenericBlock());
			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generateMobilityParameterChangeScript exception!", ex);
			Logger.getGmoLogger().printError("Error generating Mobility Parameter Change script! " + ex.getMessage());
		}
	}
	
	
	private void generate5GNR600CarrierAdd02Script(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			sb.append("Confbdl+" + eol);
			sb.append("gs+" + eol);
			sb.append(eol);

//			{	// TC_361
			String nodeType = (duInfo.isBBU || duInfo.nodeType.matches("BB.*") || duInfo.outputFormat.contentEquals("G2")) ? "BB" : duInfo.nodeType;
			sb.append(tmoCCR.generateGenericNodeNameBlock(duInfo.duName, nodeType));		// [10272020]
//			}
//			else {
//				sb.append(tmoCCR.generateGenericFingerPrintBlock(duInfo.duName));	// [05152020]
//			}

			sb.append(eol);
			sb.append(eol);

			sb.append("//////// RRU" + eol);
			sb.append(eol);

			List<String> lstFruIdListToBeUsed = new ArrayList<String>();
			if(duInfo.rndFieldReplaceableUnitIds5g.size() > 0) {
				lstFruIdListToBeUsed = duInfo.rndFieldReplaceableUnitIds5g;
			}
			else {
				lstFruIdListToBeUsed = duInfo.kgetFieldReplaceableUnitIds5g;
			}

			sb.append(eol);

			// Add a delete command for those FieldReplaceableUnit (FRU) IDs that are in KGet but not in RND.
			for(String strCurrFruIdInKGet : duInfo.kgetFieldReplaceableUnitIds5g) {
				if(!duInfo.rndFieldReplaceableUnitIds5g.contains(strCurrFruIdInKGet)) {
					sb.append("del Equipment=1,FieldReplaceableUnit=" + strCurrFruIdInKGet + "$" + eol);
				}
			}
			sb.append(eol);

			for(String strCurrFruIdInKGet : lstFruIdListToBeUsed) {
				String strCurrAugId = strCurrFruIdInKGet;

				String strDlAttenuationValToUse = "3";
				String strUlAttenuationValToUse = "3";
				String strDlTrafficDelayValToUse = "115";
				String strUlTrafficDelayValToUse = "115";

				if(duInfo.hash5GKgetFruIdTo5GCellFddNameMap.get(strCurrAugId) != null) {
					try {
						String strCellFddNameForCurrAugId = duInfo.hash5GKgetFruIdTo5GCellFddNameMap.get(strCurrAugId);
						if(!duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.dlTrafficDelay.trim().equals("")) {
							strDlTrafficDelayValToUse = duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.dlTrafficDelay;
						}

						if(!duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.ulTrafficDelay.trim().equals("")) {
							strUlTrafficDelayValToUse = duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.ulTrafficDelay;
						}

						if(!duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.dlAttenuation.trim().equals("")) {
							strDlAttenuationValToUse = duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.dlAttenuation;
						}

						if(!duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.dlTrafficDelay.trim().equals("")) {
							strUlAttenuationValToUse = duInfo.newCellToCellInfo.get(strCellFddNameForCurrAugId).tmoCellInfo.ulAttennuation;
						}
					}
					catch(Exception ex) {
						Logger.getGmoLogger().printError("Could not compute the delay and attenuation values to be used from RND. Please check your scripts.");
					}
				}

				boolean blnAddFruCreationBlock = false;
				if(!duInfo.kgetFieldReplaceableUnitIds5g.contains(strCurrAugId)) {
					blnAddFruCreationBlock = true;
				}

				// #TC_210
				blnAddFruCreationBlock = true;

				// add FieldReplaceableUnit MO for Those IDs that are in RND but not in KGet.
				if(blnAddFruCreationBlock) {
					sb.append(eol);
					sb.append(eol);
					sb.append("//////// FieldReplaceableUnit=" + strCurrAugId + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + "$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + eol);
					sb.append("administrativeState 1" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					String comment = (duInfo.isNR600) ? "//" : "";
					sb.append(comment + "set Equipment=1,FieldReplaceableUnit=" + strCurrAugId + "$ isSharedWithExternalMe true" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_1" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_1" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_2" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RiPort=DATA_2" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=A" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=A" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=B" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=B" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=C" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=C" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("pr Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=D" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=D" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					
					sb.append(eol);
					sb.append("WAIT 5" + eol);
					sb.append(eol);
				}

				String dlTrafficDelayForPrint = new String(new char[15]).replace("\0", strDlTrafficDelayValToUse + " ");
				String ulTrafficDelayForPrint = new String(new char[15]).replace("\0", strUlTrafficDelayValToUse + " ");
				String dlAttenuationForPrint = new String(new char[15]).replace("\0", strDlAttenuationValToUse + " ");
				String ulAttenuationForPrint = new String(new char[15]).replace("\0", strUlAttenuationValToUse + " ");

				sb.append(eol);
				sb.append(eol);
				sb.append("///////    AntennaUnitGroup=" + strCurrAugId + eol);
				sb.append(eol);
				sb.append(eol);

				sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + "$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=0" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=0" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=3" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=3" + eol);
				sb.append("fi" + eol);

				sb.append(eol);

				sb.append("// Create RfBranch" + eol);
				sb.append(eol);

				// RfBranch 1
				sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=1$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=1" + eol);
				sb.append("dlAttenuation " + dlAttenuationForPrint + eol);
				sb.append("dlTrafficDelay " + dlTrafficDelayForPrint + eol);
				sb.append("ulAttenuation " + ulAttenuationForPrint + eol);
				sb.append("ulTrafficDelay " + ulTrafficDelayForPrint + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("// Set rfPortRef" + eol);
				sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=1 rfPortRef Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=A" + eol);
				sb.append(eol);

				sb.append("// Set auPortRef" + eol);
				sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=1 auPortRef AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=0" + eol);
				sb.append(eol);

				// RfBranch 2
				sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=2$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=2" + eol);
				sb.append("dlAttenuation " + dlAttenuationForPrint + eol);
				sb.append("dlTrafficDelay " + dlTrafficDelayForPrint + eol);
				sb.append("ulAttenuation " + ulAttenuationForPrint + eol);
				sb.append("ulTrafficDelay " + ulTrafficDelayForPrint + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("// Set rfPortRef" + eol);
				sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=2 rfPortRef Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=C" + eol);
				sb.append("// Set auPortRef" + eol);
				sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=2 auPortRef AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2" + eol);
				sb.append(eol);

				// RfBranch 3
				sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=3$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=3" + eol);
				sb.append("dlAttenuation " + dlAttenuationForPrint + eol);
				sb.append("dlTrafficDelay " + dlTrafficDelayForPrint + eol);
				sb.append("ulAttenuation " + ulAttenuationForPrint + eol);
				sb.append("ulTrafficDelay " + ulTrafficDelayForPrint + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("// Set rfPortRef" + eol);
				sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=3 rfPortRef Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=B" + eol);
				sb.append(eol);
				sb.append("// Set auPortRef" + eol);
				sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=3 auPortRef AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1" + eol);
				sb.append(eol);

				// RfBranch 4
				sb.append("pr Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=4$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=4" + eol);
				sb.append("dlAttenuation " + dlAttenuationForPrint + eol);
				sb.append("dlTrafficDelay " + dlTrafficDelayForPrint + eol);
				sb.append("ulAttenuation " + ulAttenuationForPrint + eol);
				sb.append("ulTrafficDelay " + ulTrafficDelayForPrint + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("// Set rfPortRef" + eol);
				sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=4 rfPortRef Equipment=1,FieldReplaceableUnit=" + strCurrAugId + ",RfPort=D" + eol);
				sb.append(eol);
				sb.append("// Set auPortRef" + eol);
				sb.append("lset AntennaUnitGroup=" + strCurrAugId + ",RfBranch=4 auPortRef AntennaUnitGroup=" + strCurrAugId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=3" + eol);
				sb.append(eol);
			}
			
			//TC_295 - Add Rilink Create Portion for NR600/N41
			if(duInfo.isNR600) {
				sb.append("############################" + eol);
				sb.append("####### Create RiLink ######" + eol);
				sb.append("############################" + eol + eol);
				List<String> lstFruIdsToUse = duInfo.kgetFieldReplaceableUnitIds5g;
				if(duInfo.rndFieldReplaceableUnitIds5g != null && duInfo.rndFieldReplaceableUnitIds5g.size() > 0)	{
					lstFruIdsToUse = duInfo.rndFieldReplaceableUnitIds5g;
				}
				if(lstFruIdsToUse==null || lstFruIdsToUse.size() == 0) {
					lstFruIdsToUse = new ArrayList<String>();
					lstFruIdsToUse.add("6-01");
					lstFruIdsToUse.add("6-02");
					lstFruIdsToUse.add("6-03");
				}

				String [] arrFruIdToNumberingMap = new String [] {" ", "A", "B", "C", "D", "E"};


				for(String strCurrFruId : lstFruIdsToUse) {
					int fruIdIndex = Integer.parseInt(strCurrFruId.substring(strCurrFruId.length() - 1));
					sb.append("pr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-Data2" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-Data2" + eol);
					sb.append("FieldReplaceableUnit=BB-01,RiPort=" + arrFruIdToNumberingMap[fruIdIndex] + eol);
					sb.append("FieldReplaceableUnit=" + strCurrFruId + ",RiPort=DATA_2" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
				sb.append("wait 5" + eol + eol);
			}

			if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) {
				sb.append("############################" + eol);
				sb.append("####### Create RiLink ######" + eol);
				sb.append("############################" + eol + eol);
				List<String> lstFruIdsToUse = duInfo.kgetFieldReplaceableUnitIds5g;
				if(duInfo.rndFieldReplaceableUnitIds5g != null && duInfo.rndFieldReplaceableUnitIds5g.size() > 0)	{
					lstFruIdsToUse = duInfo.rndFieldReplaceableUnitIds5g;
				}
				String [] arrFruIdToNumberingMap = new String [] {};
				if(duInfo.tmoDUInfo.getIsMidBandAnchorScopeWith6449Radio()) {
					//Only N41 with BB6648 support all the 4 sectors on the same node
					arrFruIdToNumberingMap = new String [] {"A", "B", "C", "D", "E", "F", "G", "H"};
				}else {
					arrFruIdToNumberingMap = new String [] {"A", "B", "C", "D", "E", "F"};
				}
				for(String strCurrFruId : lstFruIdsToUse) {
					int fruIdIndex = lstFruIdsToUse.indexOf(strCurrFruId);
					String dataPort1 = "";
					String dataPort2 = "";
					String riPort = "";
					//[11202020] - AIR 6499 with DATA_2 and DATA_3
//					if(duInfo.tmoDUInfo.getIsMidBandAnchorScopeWith6449Radio()) {
//						dataPort1 = "Data3";
//						riPort = "DATA_3";
//					}else {
						dataPort1 = "Data2";
						riPort = "DATA_2";
//					}
					sb.append("pr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-" + dataPort1 + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-" + dataPort1 + eol);
					sb.append("FieldReplaceableUnit=BB-01,RiPort=" + arrFruIdToNumberingMap[fruIdIndex] + eol);
					sb.append("FieldReplaceableUnit=" + strCurrFruId + ",RiPort=" + riPort + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					//[11202020] - AIR 6499 with DATA_2 and DATA_3
//					if(duInfo.tmoDUInfo.getIsMidBandAnchorScopeWith6449Radio()) {
//						dataPort2 = "Data4";
//						riPort = "DATA_4";
//					}else {
						dataPort2 = "Data3";
						riPort = "DATA_3";
//					}
					arrFruIdToNumberingMap = (String[]) ArrayUtils.remove(arrFruIdToNumberingMap, fruIdIndex);
					sb.append("pr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-" + dataPort2 + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("cr Equipment=1,RiLink=BB-01-" + arrFruIdToNumberingMap[fruIdIndex] + "-" + strCurrFruId + "-" + dataPort2 + eol);
					sb.append("FieldReplaceableUnit=BB-01,RiPort=" + arrFruIdToNumberingMap[fruIdIndex] + eol);
					sb.append("FieldReplaceableUnit=" + strCurrFruId + ",RiPort=" + riPort + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
				sb.append("wait 5" + eol + eol);
			}

			sb.append("//////////////////////" + eol);
			sb.append("///    Sector      ///" + eol);
			sb.append("//////////////////////" + eol);
			sb.append(eol);

			for(String strCurrFruIdInKGet : lstFruIdListToBeUsed) {
				String strCurrAugId = strCurrFruIdInKGet;
				sb.append(eol);
				sb.append("pr NodeSupport=1,SectorEquipmentFunction=" + strCurrAugId + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn NodeSupport=1,SectorEquipmentFunction=" + strCurrAugId + eol);
				sb.append("administrativeState 1" + eol);
				sb.append("rfBranchRef Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=1 Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=2 Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=3 Equipment=1,AntennaUnitGroup=" + strCurrAugId + ",RfBranch=4" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);

			}
			sb.append(eol);

			sb.append("######################################" + eol);
			sb.append("# Create ServiceDiscovery MO, if needed" + eol);
			sb.append("######################################" + eol);
			sb.append(eol);
			sb.append(eol);
			sb.append("get SystemFunctions=1,SysM=1,NetconfTls=1 nodeCredential > $NCValue" + eol);
			sb.append("get SystemFunctions=1,SysM=1,NetconfTls=1 trustCategory > $TCValue" + eol);
			sb.append(eol);
			sb.append(eol);
			sb.append("pr ServiceDiscovery=1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn NodeSupport=1,ServiceDiscovery=1" + eol);
			
			
			sb.append("primaryGsds host=localhost,port=8301,serviceArea=NR" + eol);
			sb.append("secondaryGsds" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			sb.append("set NodeSupport=1,ServiceDiscovery=1 nodeCredential $NCValue" + eol);
			sb.append("set NodeSupport=1,ServiceDiscovery=1 trustCategory $TCValue" + eol);
			sb.append(eol);
			sb.append(eol);
			
			

			// #TC_210
			sb.append("pr Transport=1,SctpProfile=1$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn Transport=1,SctpProfile=1" + eol);
			sb.append("alphaIndex 3" + eol);
			sb.append("assocMaxRtx 8" + eol);
			sb.append("betaIndex 2" + eol);
			sb.append("bundlingActivated false" + eol);
			sb.append("bundlingAdaptiveActivated true" + eol);
			sb.append("bundlingTimer 10" + eol);
			sb.append("cookieLife 60" + eol);
			sb.append("dscp 24" + eol);
			sb.append("hbMaxBurst 1" + eol);
			sb.append("heartbeatActivated true" + eol);
			sb.append("heartbeatInterval 30000" + eol);
			sb.append("incCookieLife 30" + eol);
			sb.append("initARWnd 32768" + eol);
			sb.append("initRto 1000" + eol);
			sb.append("initialHeartbeatInterval 5000" + eol);
			sb.append("maxActivateThr 65535" + eol);
			sb.append("maxBurst 4" + eol);
			sb.append("maxInStreams 4" + eol);
			sb.append("maxInitRt 12" + eol);
			sb.append("maxOutStreams 4" + eol);
			sb.append("maxRto 2000" + eol);
			sb.append("maxSctpPduSize 556" + eol);
			sb.append("maxShutdownRt 5" + eol);
			sb.append("minActivateThr 1" + eol);
			sb.append("minRto 500" + eol);
			sb.append("noSwitchback false" + eol);
			sb.append("pathMaxRtx 8" + eol);
			sb.append("primaryPathAvoidance false" + eol);
			sb.append("primaryPathMaxRtx 8" + eol);
			sb.append("sackTimer 20" + eol);
			sb.append("thrTransmitBuffer 192" + eol);
			sb.append("thrTransmitBufferCongCeased 85" + eol);
			sb.append("transmitBufferSize 256" + eol);
			sb.append("userLabel 1" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			
			String sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_X2" : "1";
			sb.append("pr Transport=1,SctpEndpoint=" + sctpEndPointId + "$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn Transport=1,SctpEndpoint=" + sctpEndPointId + eol);
			sb.append("localIpAddress Transport=1,Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
			sb.append("portNumber 36422" + eol);
			sb.append("sctpProfile Transport=1,SctpProfile=1" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			
			sb.append("pr Transport=1,Router=Node_Internal_F1$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn Transport=1,Router=Node_Internal_F1" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);

			sb.append("pr Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRCUCP$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRCUCP" + eol);
			sb.append("loopback true" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);

			sb.append("pr Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRDU$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRDU" + eol);
			sb.append("loopback true" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);

			sb.append("pr Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRCUCP,AddressIPv4=1$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRCUCP,AddressIPv4=1" + eol);
			sb.append("address 169.254.42.42/32" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);

			sb.append("pr Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRDU,AddressIPv4=1$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRDU,AddressIPv4=1" + eol);
			sb.append("address 169.254.42.43/32" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);

			sb.append("pr Transport=1,SctpProfile=Node_Internal_F1$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn Transport=1,SctpProfile=Node_Internal_F1" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);

			sb.append("pr Transport=1,SctpEndpoint=F1_NRCUCP$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn Transport=1,SctpEndpoint=F1_NRCUCP" + eol);
			sb.append("localIpAddress Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRCUCP,AddressIPv4=1" + eol);
			sb.append("portNumber 38472" + eol);
			sb.append("sctpProfile Transport=1,SctpProfile=Node_Internal_F1" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);

			sb.append("pr Transport=1,SctpEndpoint=F1_NRDU$" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn Transport=1,SctpEndpoint=F1_NRDU" + eol);
			sb.append("localIpAddress Transport=1,Router=Node_Internal_F1,InterfaceIPv4=NRDU,AddressIPv4=1" + eol);
			sb.append("portNumber 38472" + eol);
			sb.append("sctpProfile Transport=1,SctpProfile=Node_Internal_F1" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);

			sb.append(eol);
			
			if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || duInfo.isNR600) {
				sb.append("###################################" + eol);
				sb.append("# SCTP endpoint used by the GNodeBFunction" + eol);
				sb.append("###################################" + eol);
				sb.append(eol);
				
				sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_X2" : "1";
				sb.append("pr Transport=1,SctpEndpoint=" + sctpEndPointId + "$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,SctpEndpoint=" + sctpEndPointId + eol);
				sb.append("localIpAddress Transport=1,Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
				sb.append("portNumber 36422" + eol);
				sb.append("sctpProfile Transport=1,SctpProfile=1" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				
				sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_N2" : "2";
				sb.append("pr Transport=1,SctpEndpoint=" + sctpEndPointId + "$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,SctpEndpoint=" + sctpEndPointId + eol);
				sb.append("localIpAddress Transport=1,Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
				sb.append("portNumber 38412" + eol);
				sb.append("sctpProfile Transport=1,SctpProfile=1" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				
				sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_Xn" : "xn";
				sb.append("pr Transport=1,SctpEndpoint=" + sctpEndPointId + "$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn Transport=1,SctpEndpoint=" + sctpEndPointId + eol);
				sb.append("localIpAddress Transport=1,Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
				sb.append("portNumber 38422" + eol);
				sb.append("sctpProfile Transport=1,SctpProfile=1" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
			}

			sb.append("//////////////////////" + eol);
			sb.append("/// Node           ///" + eol);
			sb.append("//////////////////////" + eol);
			sb.append(eol);
			
			sb.append("pr GNBDUFunction=1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn GNBDUFunction=1" + eol);
			if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.isNR600) {
				sb.append("f1SctpEndPointRef SctpEndpoint=F1_NRDU" + eol);
			}
			sb.append("gNBDUId 1" + eol);
			sb.append("gNBId " + duInfo.enbId + eol);
			sb.append("gNBIdLength 24" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			
			if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || duInfo.isNR600) {
				sb.append("pr GNBDUFunction=1,EndpointResource=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBDUFunction=1,EndpointResource=1" + eol);
				sb.append("userLabel " + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("set GNBDUFunction=1 endpointResourceRef GNBDUFunction=1,EndpointResource=1" + eol);
				sb.append(eol);

				sb.append("pr GNBDUFunction=1,EndpointResource=1,LocalSctpEndpoint=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBDUFunction=1,EndpointResource=1,LocalSctpEndpoint=1" + eol);
				sb.append("interfaceUsed 3" + eol);
				sb.append("sctpEndpointRef SctpEndpoint=F1_NRDU" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("##################################################################################" + eol);
				sb.append(eol);
			}
			
			sb.append("pr GNBCUCPFunction=1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn GNBCUCPFunction=1" + eol);
			if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.isNR600) {
				sb.append("f1SctpEndPointRef SctpEndpoint=F1_NRCUCP" + eol);
			}
			sb.append("gNBId " + duInfo.enbId + eol);
			sb.append("gNBIdLength 24" + eol);
			sb.append("pLMNId mcc=310,mnc=260" + eol);
			if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.isNR600) {
				sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_X2" : "1";
				sb.append("x2SctpEndPointRef SctpEndpoint=" + sctpEndPointId + eol);
			}
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			
			if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || duInfo.isNR600) {
				sb.append("pr GNBCUCPFunction=1,EndpointResource=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1,EndpointResource=1" + eol);
				sb.append("userLabel " + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("set GNBCUCPFunction=1 endpointResourceRef GNBCUCPFunction=1,EndpointResource=1" + eol);
				sb.append(eol);
				
				sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_Xn" : "xn";
				sb.append("pr GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=4" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=4" + eol);
				sb.append("interfaceUsed 6" + eol);
				sb.append("sctpEndpointRef SctpEndpoint=" + sctpEndPointId + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				
				sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_X2" : "1";
				sb.append("pr GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=3" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=3" + eol);
				sb.append("interfaceUsed 7" + eol);
				sb.append("sctpEndpointRef SctpEndpoint=" + sctpEndPointId + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				
				sctpEndPointId = (duInfo.isNewSite && (duInfo.nodeBandType.equals("N71") || duInfo.nodeBandType.equals("N41"))) ? "NR_N2" : "2";
				sb.append("pr GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=2" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=2" + eol);
				sb.append("interfaceUsed 4" + eol);
				sb.append("sctpEndpointRef SctpEndpoint=" + sctpEndPointId + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("pr GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=1" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1,EndpointResource=1,LocalSctpEndpoint=1" + eol);
				sb.append("interfaceUsed 3" + eol);
				sb.append("sctpEndpointRef SctpEndpoint=F1_NRCUCP" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				sb.append("##################################################################################" + eol);
				sb.append(eol);
			}
			
			sb.append("pr GNBCUUPFunction=1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn GNBCUUPFunction=1" + eol);
			sb.append("gNBId " + duInfo.enbId + eol);
			sb.append("gNBIdLength 24" + eol);
			if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.isNR600) {
				sb.append("intraRanIpAddressRef Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
			}
			sb.append("pLMNIdList mcc=310,mnc=260" + eol);
			if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.isNR600) {
				sb.append("upIpAddressRef Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1" + eol);
			}
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			
			//[10222020]
			sb.append("pr GNBCUUPFunction=1,EndpointResource=1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn GNBCUUPFunction=1,EndpointResource=1" + eol);
			sb.append("userLabel " + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			
			sb.append("set GNBCUUPFunction=1 endpointResourceRef GNBCUUPFunction=1,EndpointResource=1" + eol);
			sb.append(eol);
			
			generateLocalIpEndpointMo(duInfo, sb, "vr_TRAFFIC", "1", eol);		// Refactored 7/1/2021 GMO_TMO-101
			
			sb.append("pr GNBDUFunction=1,TermPointToGNBCUCP=1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn GNBDUFunction=1,TermPointToGNBCUCP=1" + eol);
			sb.append("ipv4Address 169.254.42.42" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);

			sb.append("//////////////////////" + eol);
			sb.append("/// Sector Carrier ///" + eol);
			sb.append("//////////////////////" + eol);

			// map the AUG Ids to the cell IDs. Sort them alphabetically and then do a 1-to-1 mapping.
			sb.append(eol);
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String currCellFddName = kvp.getKey();
				SiteCellObj currCellObj = kvp.getValue();
				String currSecEquipFunc = duInfo.map5GCellFddNameToAugIdId.get(currCellFddName);
				sb.append("pr GNBDUFunction=1,NRSectorCarrier=" + currSecEquipFunc + "-01" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBDUFunction=1,NRSectorCarrier=" + currSecEquipFunc + "-01" + eol);
				sb.append("administrativeState 0" + eol);
				sb.append("arfcnDL " + currCellObj.earfcndl + eol);
				sb.append("arfcnUL " + currCellObj.earfcnul + eol);

				long intChBw = 0;

				try
				{
					intChBw = Long.parseLong(currCellObj.channelBandwidth) / 1000; 
				}
				catch(Exception ex) { intChBw = 0;}

				sb.append("bSChannelBwDL " + intChBw + eol);
				sb.append("bSChannelBwUL " + intChBw + eol);
				//[08142020] Read configuredMaxTxPower value from RND irrespective of markets for NR600
				if (duInfo.isNR600 || duInfo.tmoDUInfo.isMidBandAnchorScope || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
					sb.append("configuredMaxTxPower " + currCellObj.configuredOutputPower + eol);
				}
				sb.append("sectorEquipmentFunctionRef SectorEquipmentFunction=" + currSecEquipFunc + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
			}

			sb.append("//////////////////////" + eol);
			sb.append("/// lock GPS       ///" + eol);
			sb.append("//////////////////////" + eol);
			sb.append(eol);
			sb.append("bl RadioEquipmentClockReference=1" + eol);
			sb.append(eol);
			sb.append("//////////////////////" + eol);
			sb.append("/// Sector Carrier ///" + eol);
			sb.append("//////////////////////" + eol);
			for(String strCurrFruId : lstFruIdListToBeUsed) {
				sb.append("pr Equipment=1,RiLink=BB-01-A-" + strCurrFruId + "-Data2" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("cr Equipment=1,RiLink=BB-01-A-" + strCurrFruId + "-Data2" + eol);
				sb.append("FieldReplaceableUnit=BB-01,RiPort=A" + eol);
				sb.append("FieldReplaceableUnit=" + strCurrFruId + ",RiPort=DATA_2" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
			}
			sb.append("//////////////////////" + eol);
			sb.append("/// NGS            ///" + eol);
			sb.append("//////////////////////" + eol);
			sb.append(eol);
			sb.append("lset SystemFunctions=1,Lm=1,FeatureState=CXC4012307 featureState 1" + eol);
			sb.append(eol);
			for(String strCurrFruId : lstFruIdListToBeUsed) {
				sb.append("set FieldReplaceableUnit=" + strCurrFruId + "$ isSharedWithExternalMe true" + eol);
			}
			sb.append(eol);
			sb.append("pr Transport=1,Synchronization=1,RadioEquipmentClock=1,NodeGroupSyncMember=1" + eol);
			sb.append("if $nr_of_mos = 0" + eol);
			sb.append("crn Transport=1,Synchronization=1,RadioEquipmentClock=1,NodeGroupSyncMember=1" + eol);
			sb.append("syncNodePriority 9" + eol);
			sb.append("syncRiPortCandidate Equipment=1,FieldReplaceableUnit=BB-01,RiPort=A" + eol);
			sb.append("end" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			sb.append("deb NodeGroupSyncMember=1" + eol);
			sb.append(eol);
			sb.append("wait 5" + eol);
			sb.append(eol);
			sb.append("////////////" + eol);
			sb.append("/// Cell ///" + eol);
			sb.append("////////////" + eol);

			String [] arrRachRootSeq = new String[] {"", "0", "32", "64", "96", "96", "96", "96", "96", "96"};
			int cellCounter = 0;
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {

				String currCellFddName = kvp.getKey();
				SiteCellObj currCellObj = kvp.getValue();
				String strGnbSecCarrPrefixToUse = duInfo.map5GCellFddNameToAugIdId.get(currCellFddName);
				// calculate the value of rachRootSequence to be used.
				String strRachRootSequenceToUse = "";

				try {
					strRachRootSequenceToUse = arrRachRootSeq[cellCounter + 1];
				}
				catch(Exception ex) {
					strRachRootSequenceToUse = "";
				}
				sb.append("pr GNBCUCPFunction=1,NRCellCU=" + currCellFddName + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1,NRCellCU=" + currCellFddName + eol);
				sb.append("cellLocalId " + currCellObj.cellId + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				
				sb.append("pr GNBDUFunction=1,NRCellDU=" + currCellFddName + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBDUFunction=1,NRCellDU=" + currCellFddName + eol);
				sb.append("administrativeState 0" + eol);
				sb.append("cellLocalId " + currCellObj.cellId + eol);
				sb.append("dl256QamEnabled true" + eol);
				sb.append("nRPCI " + currCellObj.pci + eol);
				sb.append("nRSectorCarrierRef GNBDUFunction=1,NRSectorCarrier=" + duInfo.map5GCellFddNameToAugIdId.get(currCellFddName) + "-01" + eol);
				sb.append("nRTAC " + duInfo.tac + eol);
				sb.append("pLMNIdList mcc=310,mnc=260" + eol);
				if(duInfo.isNR600) {
					sb.append("rachPreambleFormat 0" + eol);
					sb.append("rachRootSequence " + currCellObj.rachRootSequence + eol);
				}else {
					sb.append("rachRootSequence " + strRachRootSequenceToUse + eol);
				}
				sb.append("ssbDuration 1" + eol);
				sb.append("ssbFrequency 0" + eol);
				sb.append("ssbOffset 0" + eol);
				sb.append("ssbPeriodicity 20" + eol);
				sb.append("ssbSubCarrierSpacing 15" + eol);
				sb.append("subCarrierSpacing 15" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("wait 5" + eol);
				sb.append(eol);
				cellCounter++;
			}
			
			// [05042021] Removed update due to new requirement due to different parameter setting based on bands. Will be covered in NR to NR relation scripts
			/*if (CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q1")) {	// [04122021] TC_400 New MOs for 5G in 21.Q1
				sb.append(generateIntraFreqMCMcpcUeMCMosScript(duInfo, eol));				
			}*/
			
			sb.append("gs-" + eol);
			sb.append("Confbdl-" + eol);
			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNR600CarrierAdd01Script exception!", ex);
			Logger.getGmoLogger().printError("Error generating 5G NR600 CarrierAdd 01 script! " + ex.getMessage());
		}
	}
	
	private void generate2GAnd3GGRANScripts(SiteCellObj duInfo, String file, String eolType) {
		
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		Object[] cells = duInfo.gsm2G.cells.toArray();
		StringBuilder sb = new StringBuilder();
		try {
			sb.append("confb+").append(eol);
			sb.append("gs+").append(eol);
			sb.append("").append(eol);
			
			sb.append("get . ManagedElementId > $Nodename").append(eol);
			sb.append("lt all").append(eol);
			sb.append("if $Nodename != ").append(duInfo.gsm2G.cellList.get(0).nodeName).append(eol);
			sb.append(
					"print Exiting !!!!!!!!!! ABORT due to Wrong Node, or OAM IP address mismatch, or Node Name mismatch etc. !!!!!!!!!!")
					.append(eol);
			sb.append("return").append(eol);
			sb.append("else").append(eol);
			sb.append("alt").append(eol);
			sb.append("fi").append(eol);
			
			sb.append("").append(eol);
			sb.append("").append(eol);
			
			sb.append("//////// GSM IP interface Bridge").append(eol);
			sb.append("pr Transport=1,Bridge=1$").append(eol);
			sb.append("if $nr_of_mos = 0").append(eol);
			sb.append("crn Transport=1,Bridge=1").append(eol);
			sb.append("end").append(eol);
			sb.append("fi").append(eol);
			
			sb.append("//////// GSM IP interface associated with the VLAN").append(eol);
			sb.append("pr Transport=1,Router=Abis,InterfaceIPv4=1$").append(eol);
			sb.append("if $nr_of_mos = 0").append(eol);
			sb.append("crn Transport=1,Router=Abis,InterfaceIPv4=1").append(eol);
			sb.append("encapsulation Transport=1,Bridge=1").append(eol);
			sb.append("egressQosMarking QosProfiles=1,DscpPcpMap=1").append(eol);
			sb.append("loopback false").append(eol);
			sb.append("end").append(eol);
			sb.append("fi").append(eol);
			sb.append("set Transport=1,Router=Abis,InterfaceIPv4=1 encapsulation Bridge=1").append(eol);
			sb.append("set Transport=1,Bridge=1 port Transport=1,VlanPort=" + duInfo.gsm2G.AbisVlan + "").append(eol);
			
			
			sb.append("//////// RRU").append(eol);
			
			sb.append("").append(eol);
			
			//generate FieldReplaceableUnit depends on the sector count(pending)
			Set<String> sectors = new LinkedHashSet<>();
			Map<String, Integer> sectorToCarrierMap = new HashMap<>();
			//Cell Name = AE01A21
			for(String cellName : duInfo.gsm2G.cells) {
				//Sector AE01A2 ( Removed last char from cell name.for AE01A21 it will become AE01A2
				String sectorName = cellName.substring(0, cellName.length() - 1);
				sectors.add(cellName);
				int carrierId = 1;
				char lastChar = cellName.charAt(cellName.length() - 1);
				if(lastChar < 65 ) {
				 carrierId = Integer.parseInt(cellName.substring(cellName.length() - 1));
				}
				if (sectorToCarrierMap.containsKey(sectorName)) {
					Integer oldCarrierId = sectorToCarrierMap.get(sectorName);
					if (oldCarrierId != null) {
						if (carrierId < oldCarrierId) {
							sectorToCarrierMap.put(sectorName, carrierId);
						}
					}
				} else {
					sectorToCarrierMap.put(sectorName, carrierId);
				}
				
			}
			
			
			String []sectorsArray = new String[sectors.size()];
			sectorsArray = sectors.toArray(sectorsArray);
			
			for (int index = 1; index <= duInfo.gsm2G.numberOfSectors; index++) {
				//Sector Name e.g AE01A2
				String sectorName = sectorsArray[index - 1];
				//sector Id e.g AE01A2 it will be 2, remove all chars till AE01A
				char sectorCharId = sectorName.charAt(sectorName.length() - 1);
				int secId = sectorCharId - 64;
				String sectorId = secId < 10 ? "0" + secId : String.valueOf(secId);
				sb.append("//////// FieldReplaceableUnit=G-" + sectorId ).append(eol);
				
				sb.append("").append(eol);
				sb.append("pr Equipment=1,FieldReplaceableUnit=G-" + sectorId + "$").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=G-" + sectorId).append(eol);
				sb.append("administrativeState 1").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("set Equipment=1,FieldReplaceableUnit=G-" + sectorId + "$ isSharedWithExternalMe true").append(eol);

				sb.append("").append(eol);
				sb.append("pr Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RiPort=DATA_1").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RiPort=DATA_1").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);
				sb.append("pr Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RiPort=DATA_2").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RiPort=DATA_2").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RfPort=A").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RfPort=A").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RfPort=B").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RfPort=B").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RfPort=R").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RfPort=R").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);
				
				sb.append("WAIT 5 ").append(eol);

				sb.append("///////    AntennaUnitGroup=G-" + sectorId).append(eol);

				sb.append("").append(eol);
				sb.append("pr Equipment=1,AntennaUnitGroup=G-" + sectorId + "$").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=G-" + sectorId).append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,AntennaUnitGroup=G-" + sectorId + ",AntennaUnit=1").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=G-" + sectorId + ",AntennaUnit=1").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,AntennaUnitGroup=G-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=G-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,AntennaUnitGroup=G-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=G-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,AntennaUnitGroup=G-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=G-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("// Create RfBranch").append(eol);

				sb.append("").append(eol);
                 // please append cell carrier 1 values to below fields
				sb.append("pr Equipment=1,AntennaUnitGroup=G-" + sectorId + ",RfBranch=1$").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,AntennaUnitGroup=G-" + sectorId + ",RfBranch=1").append(eol);
				GsmCell gsmCell = duInfo.gsm2G.cellList.get(index - 1);
				String dlAttenuation = gsmCell.dlAttenuation;
				sb.append("dlAttenuation " + String.join(" ", Collections.nCopies(15, dlAttenuation))).append(eol);
				String dlTrafficDelay = gsmCell.dlTrafficDelay;
				sb.append("dlTrafficDelay " + String.join(" ", Collections.nCopies(15, dlTrafficDelay))).append(eol);
				String ulAttenuation = gsmCell.ulAttenuation;
				sb.append("ulAttenuation " + String.join(" ", Collections.nCopies(15, ulAttenuation))).append(eol);
				String ulTrafficDelay = gsmCell.ulTrafficDelay;
				sb.append("ulTrafficDelay " + String.join(" ", Collections.nCopies(15, ulTrafficDelay))).append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("// Set rfPortRef").append(eol);

				sb.append(
						"lset AntennaUnitGroup=G-" + sectorId + ",RfBranch=1 rfPortRef Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RfPort=A")
						.append(eol);

				sb.append("").append(eol);
				sb.append("// Set auPortRef").append(eol);

				sb.append(
						"lset AntennaUnitGroup=G-" + sectorId + ",RfBranch=1 auPortRef AntennaUnitGroup=G-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1")
						.append(eol);
				sb.append("").append(eol);
				sb.append("pr Equipment=1,AntennaUnitGroup=G-" + sectorId + ",RfBranch=2$").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,AntennaUnitGroup=G-" + sectorId + ",RfBranch=2").append(eol);
				dlAttenuation = gsmCell.dlAttenuation;
				sb.append("dlAttenuation " + String.join(" ", Collections.nCopies(15, dlAttenuation))).append(eol);
				dlTrafficDelay = gsmCell.dlTrafficDelay;
				sb.append("dlTrafficDelay " + String.join(" ", Collections.nCopies(15, dlTrafficDelay))).append(eol);
				ulAttenuation = gsmCell.ulAttenuation;
				sb.append("ulAttenuation " + String.join(" ", Collections.nCopies(15, ulAttenuation))).append(eol);
				ulTrafficDelay = gsmCell.ulTrafficDelay;
				sb.append("ulTrafficDelay " + String.join(" ", Collections.nCopies(15, ulTrafficDelay))).append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);

				sb.append("").append(eol);
				sb.append("// Set rfPortRef").append(eol);
				sb.append(
						"lset AntennaUnitGroup=G-" + sectorId + ",RfBranch=2 rfPortRef Equipment=1,FieldReplaceableUnit=G-" + sectorId + ",RfPort=B")
						.append(eol);
				sb.append("").append(eol);

				sb.append("// Set auPortRef").append(eol);
				sb.append(
						"lset AntennaUnitGroup=G-" + sectorId + ",RfBranch=2 auPortRef AntennaUnitGroup=G-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2")
						.append(eol);

				sb.append("").append(eol);

			} // loop end
			
			sb.append("//////////////////////").append(eol);
			sb.append("///    Rilinks      ///").append(eol);
			sb.append("//////////////////////").append(eol);
			sb.append("").append(eol);
			
			for (int index = 1; index <= duInfo.gsm2G.numberOfSectors; index++) {
				
				String sectorName = sectorsArray[index - 1];
				//sector Id e.g AE01A2 it will be 2, remove all chars till AE01A
				char sectorCharId = sectorName.charAt(sectorName.length() - 1 );
				int secId = sectorCharId - 64;
				String sectorId = secId < 9 ? "0" + secId : String.valueOf(secId);
				if(index > 3) {
					secId += 3;
				}
				
				//sectorDynamicChar starting from A i.e 65. 
				char sectorDynamicChar = (char)((int)64 + secId);
				
				if(sectorDynamicChar=='I') {
					sectorDynamicChar++;
				}
				
				sb.append("pr Equipment=1,RiLink=BB-01-").append(sectorDynamicChar).append("-G-" + sectorId + "-Data2").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,RiLink=BB-01-").append(sectorDynamicChar).append("-G-" + sectorId + "-Data2").append(eol);
				sb.append("FieldReplaceableUnit=BB-01,RiPort=" + sectorDynamicChar).append(eol);
				sb.append("FieldReplaceableUnit=G-" + sectorId + ",RiPort=DATA_2").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);
			}
						
			sb.append("//////////////////////").append(eol);
			sb.append("///    Sector      ///").append(eol);
			sb.append("//////////////////////").append(eol);
			sb.append("").append(eol);
			sb.append("").append(eol);
			for (int index = 1; index <= duInfo.gsm2G.numberOfSectors; index++) {
				String sectorName = sectorsArray[index - 1];
				char sectorCharId = sectorName.charAt(sectorName.length() - 1 );
				int secId = sectorCharId - 64;
				String sectorId = secId < 9 ? "0" + secId : String.valueOf(secId);
				sb.append("crn NodeSupport=1,SectorEquipmentFunction=G-" + sectorId).append(eol);
				sb.append("administrativeState 1").append(eol);
				sb.append(
						"rfBranchRef Equipment=1,AntennaUnitGroup=G-" + sectorId + ",RfBranch=1 Equipment=1,AntennaUnitGroup=G-" + sectorId + ",RfBranch=2")
						.append(eol);
				sb.append("end").append(eol);
				sb.append("").append(eol);

			}
			sb.append("").append(eol);
			
			
			sb.append("//////////////////////").append(eol);
			sb.append("///    BtsFunction ///").append(eol);
			sb.append("//////////////////////").append(eol);
			sb.append("").append(eol);
			
				
			sb.append("crn BtsFunction=1").append(eol);
			sb.append("userLabel ").append(duInfo.gsm2G.cellList.get(0).rSite).append(eol);
			sb.append("end").append(eol);
			sb.append("").append(eol);
			
			for (GsmCell cell : duInfo.gsm2G.cellList) {

				char sectorCharId = cell.name.charAt(cell.name.length() - 1 );
				int secId = sectorCharId - 64;
				String gsmSector = "1" + secId;
				sb.append("crn BtsFunction=1,GsmSector=" + gsmSector).append(eol);
				sb.append("end").append(eol);
				sb.append("").append(eol);
				// GsmSector value is carrier + sector of a cell, GsmSector value for cell
				// AE01A12 is 21.
				// gsmSectorName value for GsmSector=21 is AE01A12.
				sb.append("crn BtsFunction=1,GsmSector=" + gsmSector + ",AbisIp=1").append(eol);
				sb.append("administrativeState 0").append(eol);
				sb.append("bscBrokerIpAddress ").append(cell.bscBrokerIpAddress).append(eol);
				sb.append("dscpSectorControlUL 18").append(eol);
				sb.append("gsmSectorName ").append(cell.name).append(eol);
				sb.append("initialRetransmissionPeriod 1").append(eol);
				sb.append("ipv4Address Transport=1,Router=Abis,InterfaceIPv4=1,AddressIPv4=1").append(eol);
				sb.append("keepAlivePeriod 1").append(eol);
				sb.append("maxRetransmission 5").append(eol);
				sb.append("retransmissionCap 4").append(eol);
				sb.append("end").append(eol);
				sb.append("").append(eol);

				sb.append("crn BtsFunction=1,GsmSector=" + gsmSector + ",Trx=0").append(eol);
				sb.append("administrativeState 0").append(eol);
				sb.append("arfcnMax ").append(cell.arfcnMax).append(eol);
				sb.append("arfcnMin ").append(cell.arfcnMin).append(eol);
				sb.append("configuredMaxTxPower ").append(cell.configuredMaxTxPower).append(eol);
				sb.append("frequencyBand ").append(cell.frequencyBand).append(eol);
				sb.append("noOfRxAntennas 2").append(eol);
				sb.append("noOfTxAntennas 1").append(eol);
				String sectorId = secId < 9 ? "0" + secId : String.valueOf(secId);
				sb.append("sectorEquipmentFunctionRef NodeSupport=1,SectorEquipmentFunction=G-" + sectorId).append(eol);
				sb.append("end").append(eol);
				sb.append("").append(eol);
			}
			
			
			
//			
//			sb.append("sectorEquipmentFunctionRef NodeSupport=1,SectorEquipmentFunction=G-02").append(eol);
			
			sb.append("gs-").append(eol);
			sb.append("confb-").append(eol);
			
			FileUtil.writeToFile(sb, file);
			
		} catch (Exception e) {
			Logger.logger.error("generate GRAN G+W Scripts exception!", e);
			Logger.getGmoLogger().printError("Error while generating generate2Gand3GGRANScripts!" + e.getMessage());
		}
	}
	
	private void generate2Gand3GWRANScripts(SiteCellObj duInfo, String file, String eolType) {
		
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		Object[] cells = duInfo.wcdma3G.cells.toArray();
		StringBuilder sb = new StringBuilder();
		try {
			sb.append("confb+").append(eol);
			sb.append("gs+").append(eol);
			sb.append("").append(eol);
			sb.append("").append(eol);
			
			sb.append("get . ManagedElementId > $Nodename").append(eol);
			sb.append("lt all").append(eol);
			sb.append("if $Nodename != ").append(duInfo.gsm2G.cellList.get(0).nodeName).append(eol);
			sb.append(
					"print Exiting !!!!!!!!!! ABORT due to Wrong Node, or OAM IP address mismatch, or Node Name mismatch etc. !!!!!!!!!!")
					.append(eol);
			sb.append("return").append(eol);
			sb.append("else").append(eol);
			sb.append("alt").append(eol);
			sb.append("fi").append(eol);
			
			sb.append("").append(eol);
			sb.append("").append(eol);
			
			sb.append("//////// RRU").append(eol);
			
			sb.append("").append(eol);
			
			//generate FieldReplaceableUnit depends on the sector count(pending)
			
			Set<String> sectors = new LinkedHashSet<>();
			//Cell Name = AE01A21
			for(String cellName : duInfo.wcdma3G.cells) {
				//Sector AE01A2 ( Removed last char from cell name.for AE01A21 it will become AE01A2
				sectors.add(cellName.substring(0,cellName.length() - 1));
			}
			String []sectorsArray = new String[sectors.size()];
			sectorsArray = sectors.toArray(sectorsArray);
			
			for (int index = 1; index <= duInfo.wcdma3G.numberOfSectors; index++) {
				String cellName = (String) cells[index - 1];
				//Sector Name e.g AE01A2
				String sectorName = sectorsArray[index - 1];
				//sector Id e.g AE01A2 it will be 2, remove all chars till AE01A
				String sectorId = sectorName.substring(sectorName.length() - 1 );
				sectorId = Integer.parseInt(sectorId) < 10 ? "0" + index : index + "";
				sb.append("//////// FieldReplaceableUnit=W-" + sectorId ).append(eol);

				sb.append("").append(eol);
				sb.append("pr Equipment=1,FieldReplaceableUnit=W-" + sectorId + "$").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=W-" + sectorId).append(eol);
				sb.append("administrativeState 1").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("set Equipment=1,FieldReplaceableUnit=W-" + sectorId + "$ isSharedWithExternalMe true").append(eol);

				sb.append("").append(eol);
				sb.append("pr Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RiPort=DATA_1").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RiPort=DATA_1").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);
				sb.append("pr Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RiPort=DATA_2").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RiPort=DATA_2").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=A").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=A").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=B").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=B").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);
				
				if((duInfo.wcdma3G.ruType).contains("4415")) {
					sb.append("pr Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=C").append(eol);
					sb.append("if $nr_of_mos = 0").append(eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=C").append(eol);
					sb.append("end").append(eol);
					sb.append("fi").append(eol);
					sb.append("").append(eol);

					sb.append("pr Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=D").append(eol);
					sb.append("if $nr_of_mos = 0").append(eol);
					sb.append("crn Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=D").append(eol);
					sb.append("end").append(eol);
					sb.append("fi").append(eol);
					sb.append("").append(eol);
				}
				sb.append("pr Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=R").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("crn Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=R").append(eol);
				sb.append("end").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);
				
				sb.append("WAIT 5").append(eol);
				sb.append(eol);

				sb.append("///////    AntennaUnitGroup=W-" + sectorId).append(eol);

				sb.append("").append(eol);
				sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + "$").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=W-" + sectorId).append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);
				sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);

				sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);
				
				if((duInfo.wcdma3G.ruType).contains("4415")) {
					sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=0").append(eol);
					sb.append("if $nr_of_mos = 0").append(eol);
					sb.append("cr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=0").append(eol);
					sb.append("fi").append(eol);
					sb.append("").append(eol);

					sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=3").append(eol);
					sb.append("if $nr_of_mos = 0").append(eol);
					sb.append("cr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=3").append(eol);
					sb.append("fi").append(eol);
					sb.append("").append(eol);
				}
				
				if(!(duInfo.wcdma3G.ruType).contains("4415")) {
					sb.append("// Create RfBranch").append(eol);

					sb.append("").append(eol);

					sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=1$").append(eol);
					sb.append("if $nr_of_mos = 0").append(eol);
					sb.append("crn Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=1").append(eol);
					String dlAttenuation = "0";
					sb.append("dlAttenuation " + String.join(" ", Collections.nCopies(15, dlAttenuation))).append(eol);
					String dlTrafficDelay = "0";
					sb.append("dlTrafficDelay " + String.join(" ", Collections.nCopies(15, dlTrafficDelay))).append(eol);
					String ulAttenuation = "0";
					sb.append("ulAttenuation " + String.join(" ", Collections.nCopies(15, ulAttenuation))).append(eol);
					String ulTrafficDelay = "0";
					sb.append("ulTrafficDelay " + String.join(" ", Collections.nCopies(15, ulTrafficDelay))).append(eol);
					sb.append("end").append(eol);
					sb.append("fi").append(eol);
					sb.append("").append(eol);

					sb.append("// Set rfPortRef").append(eol);

					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=1 rfPortRef Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=A")
					.append(eol);

					sb.append("").append(eol);
					sb.append("// Set auPortRef").append(eol);

					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=1 auPortRef AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1")
					.append(eol);
					sb.append("").append(eol);
					sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=2$").append(eol);
					sb.append("if $nr_of_mos = 0").append(eol);
					sb.append("crn Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=2").append(eol);
					dlAttenuation = "0";
					sb.append("dlAttenuation " + String.join(" ", Collections.nCopies(15, dlAttenuation))).append(eol);
					dlTrafficDelay = "0";
					sb.append("dlTrafficDelay " + String.join(" ", Collections.nCopies(15, dlTrafficDelay))).append(eol);
					ulAttenuation = "0";
					sb.append("ulAttenuation " + String.join(" ", Collections.nCopies(15, ulAttenuation))).append(eol);
					ulTrafficDelay = "0";
					sb.append("ulTrafficDelay " + String.join(" ", Collections.nCopies(15, ulTrafficDelay))).append(eol);
					sb.append("end").append(eol);
					sb.append("fi").append(eol);

					sb.append("").append(eol);
					sb.append("// Set rfPortRef").append(eol);
					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=2 rfPortRef Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=B")
					.append(eol);
					sb.append("").append(eol);

					sb.append("// Set auPortRef").append(eol);
					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=2 auPortRef AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2")
					.append(eol);
					sb.append("").append(eol);
				}
				
				else {
					sb.append("// Create RfBranch").append(eol);

					sb.append("").append(eol);

					sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=1$").append(eol);
					sb.append("if $nr_of_mos = 0").append(eol);
					sb.append("crn Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=1").append(eol);
					String dlAttenuation = "0";
					sb.append("dlAttenuation " + String.join(" ", Collections.nCopies(15, dlAttenuation))).append(eol);
					String dlTrafficDelay = "0";
					sb.append("dlTrafficDelay " + String.join(" ", Collections.nCopies(15, dlTrafficDelay))).append(eol);
					String ulAttenuation = "0";
					sb.append("ulAttenuation " + String.join(" ", Collections.nCopies(15, ulAttenuation))).append(eol);
					String ulTrafficDelay = "0";
					sb.append("ulTrafficDelay " + String.join(" ", Collections.nCopies(15, ulTrafficDelay))).append(eol);
					sb.append("end").append(eol);
					sb.append("fi").append(eol);
					sb.append("").append(eol);

					sb.append("// Set rfPortRef").append(eol);

					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=1 rfPortRef Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=A")
					.append(eol);

					sb.append("").append(eol);
					sb.append("// Set auPortRef").append(eol);

					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=1 auPortRef AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=0")
					.append(eol);
					sb.append("").append(eol);
					sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=2$").append(eol);
					sb.append("if $nr_of_mos = 0").append(eol);
					sb.append("crn Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=2").append(eol);
					dlAttenuation = "0";
					sb.append("dlAttenuation " + String.join(" ", Collections.nCopies(15, dlAttenuation))).append(eol);
					dlTrafficDelay = "0";
					sb.append("dlTrafficDelay " + String.join(" ", Collections.nCopies(15, dlTrafficDelay))).append(eol);
					ulAttenuation = "0";
					sb.append("ulAttenuation " + String.join(" ", Collections.nCopies(15, ulAttenuation))).append(eol);
					ulTrafficDelay = "0";
					sb.append("ulTrafficDelay " + String.join(" ", Collections.nCopies(15, ulTrafficDelay))).append(eol);
					sb.append("end").append(eol);
					sb.append("fi").append(eol);

					sb.append("").append(eol);
					sb.append("// Set rfPortRef").append(eol);
					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=2 rfPortRef Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=C")
					.append(eol);
					sb.append("").append(eol);

					sb.append("// Set auPortRef").append(eol);
					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=2 auPortRef AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=2")
					.append(eol);
					sb.append("").append(eol);
					sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=3$").append(eol);
					sb.append("if $nr_of_mos = 0").append(eol);
					sb.append("crn Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=3").append(eol);
					dlAttenuation = "0";
					sb.append("dlAttenuation " + String.join(" ", Collections.nCopies(15, dlAttenuation))).append(eol);
					dlTrafficDelay = "0";
					sb.append("dlTrafficDelay " + String.join(" ", Collections.nCopies(15, dlTrafficDelay))).append(eol);
					ulAttenuation = "0";
					sb.append("ulAttenuation " + String.join(" ", Collections.nCopies(15, ulAttenuation))).append(eol);
					ulTrafficDelay = "0";
					sb.append("ulTrafficDelay " + String.join(" ", Collections.nCopies(15, ulTrafficDelay))).append(eol);
					sb.append("end").append(eol);
					sb.append("fi").append(eol);
					sb.append("").append(eol);

					sb.append("// Set rfPortRef").append(eol);
					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=3 rfPortRef Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=B")
					.append(eol);
					sb.append("").append(eol);
					sb.append("// Set auPortRef").append(eol);
					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=3 auPortRef AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=1")
					.append(eol);
					sb.append("").append(eol);
					sb.append("pr Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=4$").append(eol);
					sb.append("if $nr_of_mos = 0").append(eol);
					sb.append("crn Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=4").append(eol);
					dlAttenuation = "0";
					sb.append("dlAttenuation " + String.join(" ", Collections.nCopies(15, dlAttenuation))).append(eol);
					dlTrafficDelay = "0";
					sb.append("dlTrafficDelay " + String.join(" ", Collections.nCopies(15, dlTrafficDelay))).append(eol);
					ulAttenuation = "0";
					sb.append("ulAttenuation " + String.join(" ", Collections.nCopies(15, ulAttenuation))).append(eol);
					ulTrafficDelay = "0";
					sb.append("ulTrafficDelay " + String.join(" ", Collections.nCopies(15, ulTrafficDelay))).append(eol);
					sb.append("end").append(eol);
					sb.append("fi").append(eol);
					sb.append("").append(eol);
					sb.append("// Set rfPortRef").append(eol);
					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=4 rfPortRef Equipment=1,FieldReplaceableUnit=W-" + sectorId + ",RfPort=D")
					.append(eol);
					sb.append("").append(eol);
					sb.append("// Set auPortRef").append(eol);
					sb.append(
							"lset AntennaUnitGroup=W-" + sectorId + ",RfBranch=4 auPortRef AntennaUnitGroup=W-" + sectorId + ",AntennaUnit=1,AntennaSubunit=1,AuPort=3")
					.append(eol);
				}
				sb.append("").append(eol);
				sb.append("").append(eol);
				sb.append("").append(eol);
				
				

			} // loop end
			
			sb.append("//////////////////////").append(eol);
			sb.append("///    Rilinks      ///").append(eol);
			sb.append("//////////////////////").append(eol);
			sb.append("").append(eol);
			char p='D';
			for (int index = 1; index <= duInfo.wcdma3G.numberOfSectors; index++) {
				String sectorId = index < 10 ? "0" + index : String.valueOf(index);
				sb.append("pr Equipment=1,RiLink=BB-01-" + p + "-W-" + sectorId + "-Data1").append(eol);
				sb.append("if $nr_of_mos = 0").append(eol);
				sb.append("cr Equipment=1,RiLink=BB-01-" + p + "-W-" + sectorId + "-Data1").append(eol);
				sb.append("FieldReplaceableUnit=BB-01,RiPort=" + p).append(eol);
				sb.append("FieldReplaceableUnit=W-" + sectorId + ",RiPort=DATA_1").append(eol);
				sb.append("fi").append(eol);
				sb.append("").append(eol);
				if(index == 3) {
					p='J';
				}
				p++;
			}
			
			sb.append("").append(eol);
			
			sb.append("//////////////////////").append(eol);
			sb.append("///    Sector      ///").append(eol);
			sb.append("//////////////////////").append(eol);
			sb.append("").append(eol);
			sb.append("").append(eol);
			for (int index = 1; index <= duInfo.wcdma3G.numberOfSectors; index++) {
				String sectorId = index < 10 ? "0" + index : String.valueOf(index);
				sb.append("crn NodeSupport=1,SectorEquipmentFunction=W-" + sectorId).append(eol);
				sb.append("administrativeState 1").append(eol);
				if((duInfo.wcdma3G.ruType).contains("4415")) {
					sb.append(
							"rfBranchRef Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=1 Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=2 "
									+ "Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=3 Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=4")
							.append(eol);
				}
				else {
					sb.append(
							"rfBranchRef Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=1 Equipment=1,AntennaUnitGroup=W-" + sectorId + ",RfBranch=2")
							.append(eol);
				}
				sb.append("end").append(eol);
				sb.append("").append(eol);

			}
			sb.append("").append(eol);
			if(duInfo.wcdma3G!=null && duInfo.wcdma3G.cellList!=null && !duInfo.wcdma3G.cellList.isEmpty()) {
				sb.append("crn NodeBFunction=1,NodeBLocalCellGroup=1").append(eol);
				sb.append("end").append(eol);
				sb.append("#END NodeBFunction=1,NodeBLocalCellGroup=1 --------------------").append(eol);
			}
			sb.append(eol);
			
			
			for (int index = 0; index < duInfo.wcdma3G.numberOfSectors; index++) {
				String sectorName = sectorsArray[index];
				String sectorId = sectorName.substring(sectorName.length() - 1 );
				String sectorId1 = index < 10 ? "0" + (index+1) : String.valueOf(index);
				sb.append("crn NodeBFunction=1,NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1").append(eol);
				sb.append("localCellId " + duInfo.wcdma3G.cellList.get(index).cellIdentity).append(eol);
				sb.append("operatingBand " + duInfo.wcdma3G.cellList.get(index).Band).append(eol);
				sb.append("uarfcnDl " + duInfo.wcdma3G.cellList.get(index).uarfcnDl).append(eol);
				sb.append("userLabel " + duInfo.wcdma3G.cellList.get(index).name).append(eol);
				sb.append("end").append(eol);
				sb.append("#END NodeBFunction=1,NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1" + " --------------------").append(eol);
				sb.append(eol);
				sb.append("crn NodeBFunction=1,NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1" + ",NodeBSectorCarrier=C1").append(eol);
				sb.append("configuredMaxTxPower " + Integer.parseInt(duInfo.wcdma3G.cellList.get(index).MaxtotalOutputPower)*1000).append(eol);
				sb.append("numOfRxAntennas 2").append(eol);
				sb.append("numOfTxAntennas 2").append(eol);
				sb.append("sectorEquipmentFunctionRef NodeSupport=1,SectorEquipmentFunction=W-" + sectorId1).append(eol);
				sb.append("latitude " + duInfo.gsm2G.latitude).append(eol);
				sb.append("longitude " + duInfo.gsm2G.longitude).append(eol);		
				sb.append("end").append(eol);
				sb.append("#END NodeBFunction=1,NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1,NodeBSectorCarrier=C1 " + "--------------------").append(eol);
			}
			sb.append(eol);
			sb.append(eol);
			
			sb.append("////latitude//////longitude////" + eol);
			for (int index = 0; index < duInfo.wcdma3G.numberOfSectors; index++) {
				String sectorName = sectorsArray[index];
				String sectorId = sectorName.substring(sectorName.length() - 1);
				sb.append("Set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1"
						+ ",NodeBSectorCarrier=C1" + " latitude " + duInfo.gsm2G.latitude + eol);
			}
			for (int index = 0; index < duInfo.wcdma3G.numberOfSectors; index++) {
				String sectorName = sectorsArray[index];
				String sectorId = sectorName.substring(sectorName.length() - 1);
				String sectorId1 = index < 10 ? "0" + (index + 1) : String.valueOf(index);
				sb.append("Set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1"
						+ ",NodeBSectorCarrier=C1" + " longitude " + duInfo.gsm2G.longitude + eol);
			}
			
			ArrayList<HashMap<String, String>> wcdmaDynRowDataArray = CSVUtils
					.readDataRowArrayFromCSVFile(CSVUtils.getCIQCSVFile("WCDMA"), "SITE NAME", duInfo.duName);
			for (HashMap<String, String> map : wcdmaDynRowDataArray) {
				String cellId = map.get("UtranCellId");
				String beamDir = map.get("beamDirection");
				if(beamDir!=null && beamDir.length() == 2) {
					beamDir = "0" + beamDir;
				}
				else if(beamDir!=null && beamDir.length() == 1) {
					beamDir = "00" + beamDir;
				}
				sb.append("Set NodeBLocalCellGroup=1,NodeBLocalCell=S" + cellId.substring(cellId.length()-2,cellId.length()-1) + "C1"
						+ ",NodeBSectorCarrier=C1" + " beamDirection " + beamDir + eol);
				
			}
			
			for (HashMap<String, String> map : wcdmaDynRowDataArray) {
				String cellId = map.get("UtranCellId");
				sb.append("Set NodeBLocalCellGroup=1,NodeBLocalCell=S" + cellId.substring(cellId.length()-2,cellId.length()-1) + "C1"
						+ ",NodeBSectorCarrier=C1" + " height " + map.get("height") + eol);
				
			}
				
			sb.append(eol);
			sb.append(eol);
			if(duInfo.wcdma3G!=null && duInfo.wcdma3G.cellList!=null && !duInfo.wcdma3G.cellList.isEmpty()) {
				sb.append("//set IubDataStreams hsDataFrameDelayThreshold 200" + eol
						+ "//set IubDataStreams schHsFlowControlOnOff 0,1,1,1,1,0,1,0,0,0,0,0,0,0,0,0" + eol
						+ "set NodeBFunction eulMaxAllowedSchRate 5120" + eol
						+ "set NodeBFunction eulMaxShoRate 5760" + eol
						+ "//set NodeBFunction eulNonServHwRate 128" + eol
						+ "//set NodeBFunction eulNoReschUsers 5" + eol
						+ "//set NodebFunction eulSchedulingWeight 1,440,1100,2200,4400,5500,8800,6600,1700,4000,2750,3300,1,3850,550,10000" + eol
						+ "//set NodebFunction eulTargetRate 128" + eol
						+ "set NodeBFunction eul2msFirstSchedStep 20" + eol
						+ "//set NodeBFunction eulDchMaxAllowedSchRate 1600" + eol
						+ "//set NodeBFunction eulFachInitialRate 34" + eol);
			}
			
			sb.append("//////////////////////").append(eol);
			sb.append("///    NGS         ///").append(eol);
			sb.append("//////////////////////").append(eol);
			sb.append("crn Transport=1,Synchronization=1,RadioEquipmentClock=1,NodeGroupSyncMember=1").append(eol);
			sb.append("administrativeState 1").append(eol);
			sb.append("syncNodePriority 5").append(eol);
			int counter = 0;
			if (duInfo.wcdma3G != null && duInfo.wcdma3G.cellList != null && !duInfo.wcdma3G.cellList.isEmpty()) {
				// Excalibur_211
				char riPort = 'D';
				for (int index = 1; index <= duInfo.wcdma3G.numberOfSectors; index++) {
					sb.append("syncRiPortCandidate Equipment=1,FieldReplaceableUnit=BB-01,RiPort=" + riPort).append(eol);

					if (index == 3) {
						riPort = 'J';
					}
					riPort++;
				}
			}

			if (duInfo.gsm2G != null && duInfo.gsm2G.cellList != null && !duInfo.gsm2G.cellList.isEmpty()) {
				// Excalibur_211
				char riPort = 'A';
				//if UTMS is absent, then print based on GSM Excalibur_214								
				for (int index = 1; index <= duInfo.gsm2G.numberOfSectors; index++) {
					if (riPort == 'I') {
						riPort = 'J';
					}

					sb.append("syncRiPortCandidate Equipment=1,FieldReplaceableUnit=BB-01,RiPort=" + riPort).append(eol);

					if (index == 3) {
						riPort = 'F';
					}
					riPort++;
				}

			}

			sb.append("userLabel").append(eol);
			sb.append("end").append(eol);
			sb.append(eol);
			
			sb.append(eol);
			sb.append("///    feature activation").append(eol);
			sb.append("set FeatureState=CXC4012016 featureState 1").append(eol);
			sb.append("set FeatureState=CXC4012017 featureState 1").append(eol);
			sb.append("set FeatureState=CXC4020051 featureState 1").append(eol);
			sb.append("set FeatureState=CXC4012026 featureState 1").append(eol);

			//Added on 5/27 per RF feedback
			sb.append(eol);
			if(duInfo.wcdma3G!=null && duInfo.wcdma3G.cellList!=null && !duInfo.wcdma3G.cellList.isEmpty()) {
				sb.append("lset NodeBFunction=1,NodeBLocalCellGroup=1,NodeBLocalCell= maxNumHsPdschCodes 15").append(eol);
				sb.append("lset NodeBFunction=1,NodeBLocalCellGroup=1,NodeBLocalCell= featCtrlEnhancedLayer2 1").append(eol);
				sb.append("lset NodeBFunction=1,NodeBLocalCellGroup=1,NodeBLocalCell= featCtrlHsdpaDynamicCodeAllocation 1").append(eol);
			}
			if(duInfo.wcdma3G!=null && duInfo.wcdma3G.cellList!=null && !duInfo.wcdma3G.cellList.isEmpty()) {

				for (int index = 0; index < duInfo.wcdma3G.numberOfSectors; index++) {
					int sectorId = index + 1;
					sb.append("set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 eulMaxTdUsers 8 " + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 eulMinMarginCoverage 10 " + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlCpc 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlCpc 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlCpc 1 " + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlEnhUeDrx 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlEulFach  1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlEulMc 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlFDpchSrbOnHsdpa 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlHsAdaptiveBler  1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlHsdpaDbMc 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlHsdpaDynamicCodeAllocation 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlHsdpaIncrementalRedundancy 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlHsdpaMc 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlHsdpaPowerSharing 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlHsFach 1" + eol
							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlImprovedLayer2 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 featCtrlNbir 1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 maxNumEulUsers 128" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 maxNumHsdpaUsers 128" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1 queueSelectAlgorithm 2" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1,NodeBSectorCarrier=C1 eulNoiseFloorLock -1" + eol

							+ "set NodeBLocalCellGroup=1,NodeBLocalCell=S" + sectorId + "C1,NodeBSectorCarrier=C1 nbirAlgorithm 4" + eol);
				}


			}
			
			if(duInfo.wcdma3G!=null && duInfo.wcdma3G.cellList!=null && !duInfo.wcdma3G.cellList.isEmpty()) {
				sb.append(eol);
				sb.append(eol);
				sb.append("set NodeBFunction=1,Iub=1 userLabel " + duInfo.wcdma3G.rncName).append(eol);
			}
			sb.append(eol);
			sb.append("gs-").append(eol);
			sb.append("confb-").append(eol);
			
			FileUtil.writeToFile(sb, file);
			
		} catch (Exception e) {
			Logger.logger.error("generate WRAN G+W Scripts exception!", e);
			Logger.getGmoLogger().printError("Error while generating generate2Gand3GWRANScripts!" + e.getMessage());
		}
	}
	
	private void generateBscCellData(SiteCellObj duInfo, String fileName) {
		
		try {
			StringBuilder sb = new StringBuilder();
			sb.append("!************************************************************************!" + eol);
			sb.append("!*****************************CELL DT*******************************!" + eol);
			sb.append("!************************************************************************!" + eol);
			// BTS NAME & BSC NAME referred from Transport_CIQLess
			sb.append("!*  BTS NAME      :  " + duInfo.gsm2G.cellList.get(0).btsName + "                        *!" + eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
			sb.append("!*  BSC      	 :  " + cell.bsc + "                        *!" + eol);
			}
			sb.append("!*  RBS TYPE      :                         *!" + eol);
			
			fileName =  fileName + File.separator + "P1_1a_" + duInfo.gsm2G.cellList.get(0).bsc + "_" + duInfo.gsm2G.cellList.get(0).rSite + "_NewSiteAdd_DT.txt";
			Logger.getGmoLogger().printTextWithTimeStamp("creating " + fileName);
			Map<String, Integer> configMap =  new LinkedHashMap<>();
			for(GsmCell cell: duInfo.gsm2G.cellList) {
				String cellName = cell.name;
				String sector = cellName.substring(0, cellName.length() - 1);
				if(configMap.containsKey(sector)) {
					configMap.put(sector, configMap.get(sector) + 1);
				}else {
					configMap.put(sector, 1);
				}
			}
			
			Collection<Integer> configValues = configMap.values();
			String siteConfigString = "";
			for(Integer value : configValues) {
				siteConfigString +=  String.valueOf(value) + " + ";
			}
			
			if(siteConfigString.trim().endsWith(" + ")) {
				siteConfigString = siteConfigString.trim().substring(0, siteConfigString.trim().length() -1 );
			}
			sb.append("!*  SITE CONFIG   :  " + siteConfigString + "                       *!" + eol);
			sb.append("!*  PREPARED BY   :  " + CommonUtil.userName() + "                        *!" + eol);
			sb.append("!*  PROJECT NAME  :  T-Mobile CELL SITE SWAP        *!" + eol);
			sb.append("!*----------------------------------------------------------------------*!" + eol);
			sb.append("!*                      REVISION    :   A                               *!" + eol);
			sb.append("!*----------------------------------------------------------------------*!" + eol);
			sb.append("!************************************************************************!" + eol);
			
			//sb.append(sbScriptHeaderText + eol);
			
			sb.append("!IF ANY PARAMETER MISSING IN DT, KINDLY CHECK AND CONFIRM BEFORE LOADING !" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                      DEFINITION OF CELL NAME                       **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLDEI:CELL=" + cell.name + ", CSYSTYPE=" + cell.csysType + ";" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                DEFINITION OF CELL DESCRIPTION DATA                 **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!**  				NEWNAME = NEWCELLNAME                             **;" + eol);
			sb.append("!**     CHANGE CGI & BSIC & BCCHNO & BCCHTYPE ACCORDING TO CDD         **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!KINDLY CHECK & CONFIRM THE PARAMETERS AS PER REQUIREMENT   !" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				if(cell.bsic.length() == 1) {
					Logger.getGmoLogger().printWarning("BSIC value for the cell = " + cell.name + " is not in standard format.Please check the value");
				}
				sb.append("RLDEC:CELL=" + cell.name + ", CGI=" + cell.cgi + ", BSIC=" + cell.ncc+cell.bcc + ", BCCHNO=" + cell.bcchno + ", BCCHTYPE=NCOMB,AGBLK=1,MFRMS=4,FNOFFSET=0,IRC=ON;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                  ACTIVATE ADAPTIVE CONFIGURATION                   **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLACI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**             CONNECT CELL TO CHANNEL ALLOCATION PROFILE             **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLHPC:CELL=" + cell.name + ",CHAP=1;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                 CONFIGURATION CONTROL CHANNEL DATA                 **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLCCC:CELL=" + cell.name + ",CHGR=0,SDCCH=1,TN=2,CBCH=YES;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                  CONFIGURATION FREQUENCY HOPPING                   **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLCHC:CELL=" + cell.name + ",CHGR=0,HOP=OFF;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                      CONFIGURATION POWER DATA                      **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!CHECK FOR MSTXPWR & BSPWRT & BSPWRB (USUALLY 30 & 45 & 45) *** for microcell use BSPWRT=33,BSPWRB=33 ***;");
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLCPC:CELL=" + cell.name + ",BSPWRT=" + cell.bspwrt + ",BSPWRB=" + cell.bspwrb + ",MSTXPWR=30;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                     CONFIGURATION DTX DOWNLINK                     **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLCXC:CELL=" + cell.name + ",DTXD=ON;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                         CELL LOCATING DATA                         **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!CHECK FOR BSPWR, BSRXMIN, BSRXSUFF, MSRXMIN, MSRXSUFF, & BSTXPWR (USUALLY 57, 150, 150, 102, 0, & 57) ;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				
				sb.append("RLLOC:CELL=" + cell.name + ",BSPWR=" + cell.bspwr + ",BSTXPWR=" + cell.bstxpwr + ",BCCHDTCBN=20,BCCHLOSS=200,BCCHREUSE=TIGHT,BSRXMIN=150;" + eol);
				sb.append("RLLOC:CELL=" + cell.name + ",BSRXSUFF=150,MSRXMIN=102,MSRXSUFF=0,SCHO=OFF,MISSNM=3,AW=ON;" + eol);
				sb.append("RLLOC:CELL=" + cell.name + ",HYSTSEP=85,ISHOLEV=20;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                     CELL LOCATING URGENCY DATA                     **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLLUC:CELL=" + cell.name + ",TALIM=62,CELLQ=HIGH,QLIMUL=50,QLIMDL=50,QLIMULAFR=60,QLIMDLAFR=60;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                     CELL LOCATING PENALTY DATA                     **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLLPC:CELL=" + cell.name + ",PTIMHF=5,PTIMBQ=15,PTIMTA=30,PSSHF=63,PSSBQ=7,PSSTA=63;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                     CELL LOCATING FILTER DATA                      **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLLFC:CELL=" + cell.name + ",SSEVALSD=6,QEVALSD=6,SSEVALSI=6,QEVALSI=6,SSLENSD=10,QLENSD=10,SSLENSI=4,QLENSI=4,SSRAMPSD=5,SSRAMPSI=1;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                   CELL LOCATING DISCONNECT DATA                    **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLLDC:CELL=" + cell.name + ",MAXTA=63,RLINKUP=32,RLINKUPAFR=40,RLINKUPAHR=40;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                  CELL LOCATING HIERARCHICAL DATA                   **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!RLLHC:CELL=" + cell.name + ",LAYER=2,LAYERTHR=95,LAYERHYST=2,PSSTEMP=0,PTIMTEMP=0,FASTMSREG=OFF;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                     CELL LOCATING INTRACELL HO                     **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLIHC:CELL=" + cell.name + ",IHO=ON,TMAXIHO=7,TIHO=10,MAXIHO=2,SSOFFSETULN=10,SSOFFSETDLN=10,SSOFFSETULAFRN=10,SSOFFSETDLAFRN=10;" + eol);
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLIHC:CELL=" + cell.name + ", QOFFSETULAFRN=5, QOFFSETDLAFRN=5, QOFFSETDLN=5, QOFFSETULN=10;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**               SYSTEM INFORMATION SACCH AND BCCH DATA               **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!CHECK FOR ACCMIN, CCHPWR, DTXU, & NCCPERM (USUALLY 105, 30, 1, & 0&&7) ;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLSSC:CELL=" + cell.name + ",NCCPERM=0&1&2&3&4&5&6&7,ACCMIN=102,CCHPWR=30,CRH=6,DTXU=1,RLINKT=32,NECI=1,RLINKTAFR=40,RLINKTAHR=40;" + eol);
				
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                    SYSTEM INFORMATION BCCH DATA                    **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLSBC:CELL=" + cell.name + ",CB=NO,CBQ=HIGH,ACC=CLEAR,MAXRET=4,TX=32,ATT=YES,T3212=10,CRO=0,TO=0,PT=0,ECSC=YES;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                 DYNAMIC MS POWER CONTROL CELL DATA                 **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLPCC:CELL=" + cell.name + ",SSDESUL=92,QDESUL=30,LCOMPUL=10,QCOMPUL=60;" + eol);
			}
			sb.append(eol);
			sb.append("!If you receive fault code 139 for RLPCI the function Dynamic MS Power Control is already activated. ;" + eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLPCI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                DYNAMIC BTS POWER CONTROL CELL DATA                 **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLBCC:CELL=" + cell.name + ",SSDESDL=90,QDESDL=35,LCOMPDL=5,QCOMPDL=55,BSPWRMINN=20;" + eol);
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLBCI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**            SUPERVISION OF LOGICAL CHANNELS AVAILABILITY            **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!CHECK & SET LIMIT VALUE OF AVAILABILITY ALARM THRESHOLDS ;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLSLC:CELL=" + cell.name + ",LVA=0,ACL=A3,CHTYPE=TCH,CHRATE=HR;" + eol);
				sb.append("RLSLC:CELL=" + cell.name + ",LVA=0,ACL=A1,CHTYPE=SDCCH;" + eol);
				sb.append("RLSLC:CELL=" + cell.name + ",LVA=1,ACL=A1,CHTYPE=BCCH;" + eol);
				sb.append("RLSLC:CELL=" + cell.name + ",LVA=1,ACL=A2,CHTYPE=CBCH;" + eol);
				sb.append(eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                      IDLE CHANNEL MEASUREMENT                      **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLIMC:CELL=" + cell.name + ",INTAVE=6,LIMIT1=2,LIMIT2=8,LIMIT3=12,LIMIT4=20;" + eol);
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLIMI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                         CELL LOAD SHARING                          **;" + eol);
			sb.append("!************************************************************************;" + eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				
				sb.append("RLLCC:CELL=" + cell.name + ",CLSACC=30,CLSLEVEL=15,RHYST=75,CLSRAMP=8,HOCLSACC=ON;" + eol);	
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLLCI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**         ADAPTIVE CONFIGURATION OF LOGICAL CHANNELS (SDCCH)         **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLACC:CELL=" + cell.name + ",SLEVEL=1,STIME=20;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                    DEFINITION OF CHANNEL GROUP                     **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!RLDGI:CELL=" + cell.name + ",CHGR=1;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**              DEFINITION OF HANDOVER POWER BOOST DATA               **;" + eol);
			sb.append("!**             (JUST DEFINED UNDER COMMERCIAL AGREEMENT)              **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLPBI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                    ACTIVATION OF GPRS IN CELLS                     **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLGSI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {	
				sb.append("RLGSC:CELL=" + cell.name + ",FPDCH=1,GAMMA=18,PSKONBCCH=ENABLED,PRIMPLIM=8,SCALLOC=UL;" + eol);			
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLGSC:CELL=" + cell.name + ", E2AINITMCS=3, E2ALQC=OFF, EINITMCS=3, RTTIINITMCS=5;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                    CELL MEASUREMENT FREQUENCIES                    **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!MBCCHNO IS BCCH OF OTHER TWO CELLS (MEASUREMENT on BROADCAST CONTROL CHANNEL #) ;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!Total No. of MBCCH values for " + cell.name + " : " + (cell.mbcchno.split("&").length + 1) + "!" + eol);
				sb.append("RLMFC:CELL=" + cell.name + ",MBCCHNO=" + cell.mbcchno + ";" + eol);
				sb.append(eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                  CONFIGURATION FREQUENCY HOPPING                   **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!CHECK FOR HSN & MAIO;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!RLCHC:CELL=" + cell.name + ",CHGR=1,HOP=,HSN=,MAIO=;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                    CONFIGURATION FREQUENCY DATA                    **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!CHECK DCHNO= HOPPING FREQUENCIES ;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!RLCFI:CELL=" + cell.name + ",CHGR=1,DCHNO=;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**              CONFIGURATION CONTROL CHANNEL DATA FOR CHGR=1         **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!RLCCC:CELL=" + cell.name + ",CHGR=1,SDCCH=,TN=0;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                    CELL CONFIGURATION BPC DATA                     **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLBDC:CELL=" + cell.name + ",CHGR=0,NUMREQBPC=8,NUMREQEGPRSBPC=4,TN7BCCH=EGPRS;" + eol);
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!RLBDC:CELL=" + cell.name + ",CHGR=1,NUMREQBPC=0,NUMREQEGPRSBPC=;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                    CELL CHANNEL ALLOCATION DATA                    **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {	
				sb.append("RLCLC:CELL=" + cell.name + ",CSPSALLOC=CSLASTPSFIRST,GPRSPRIO=0;" + eol); //Excalibur_215
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                    SET AMR PARAMETERS                              **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!ONLY needed when DMSUPP is ON;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!RLDMI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {	
				sb.append("RLDMC:CELL=" + cell.name + ",DMTHAMR=100;" + eol);
					
			}
			sb.append(eol);
			sb.append("!ONLY needed when DHA is ON;" + eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLDHC:CELL=" + cell.name + ",DHA=ON,DTHAMR=100,DTHNAMR=0;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                  INITIATE AMR POWER CONTROL CELL                   **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLAPI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                   CHANGE AMR POWER CONTROL CELL                    **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLAPC:CELL=" + cell.name + ",SSDESDLAFR=90,QDESDLAFR=40,SSDESULAFR=92,QDESULAFR=35,QDESDLAHR=35,QDESULAHR=35,SSDESDLAHR=90,SSDESULAHR=92;" + eol);
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLAPC:CELL=" + cell.name + ",QDESULAWB=40,QDESDLAWB=40,SSDESDLAWB=90;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                   INITIATE FAST RETURN to WCDMA                    **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLRWI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			sb.append("!************************************************************************;" + eol
					+ "!**                   INITIATE FAST RETURN to LTE                    **;" + eol
					+ "!************************************************************************;" + eol);
			
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLRLI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                   REDUCED POWER AFTER HO                           **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			sb.append("!REDUCED BTS POWER AFTER HO!" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLBRI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLBRC:CELL=" + cell.name + ",BSRPWROFFSETN=2;" + eol);
			}
			sb.append(eol);
			sb.append("!REDUCED MS POWER AFTER HO!" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLMRI:CELL=" + cell.name + ";" + eol);
			}
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLMRC:CELL=" + cell.name + ",MSRPWROFFSETN=2;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**       CELL NETWORK CONTROLLED CELL RESELECTION PROFILE DATA        **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!NOT SUPPORTED, Kindly check & unblock the command as per the requirement!" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!RLNPI:CELL=" + cell.name + ",NCPROF=1;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**         CELL NETWORK CONTROLLED CELL RESELECTION MODE DATA         **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLNMI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLNMC:CELL=" + cell.name + ",NCRPT=2;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                  SMS Cell Broadcast DRX                            **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!RLMDI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!RLMDC:CELL=" + cell.name + ", FSLOTS=4, SPERIOD=40;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**            PACKET SWITCHED DOWNLINK POWER CONTROL DATA             **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RFPCI:CELL=" + cell.name + ",DLPCG,DLPCE2A;" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**              SEIZURE SUPERVISION OF LOGICAL CHANNELS               **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLVLI:CELL=" + cell.name + ",CHTYPE=TCH;" + eol);
				sb.append("RLVLI:CELL=" + cell.name + ",CHTYPE=SDCCH;" + eol);
				sb.append(eol);
			}
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**        SUPERVISION OF LOGICAL CHANNEL AVAILABILITY INITIATE        **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLSLI:CELL=" + cell.name + ";" + eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                  SYSTEM INFORMATION BCCH MESSAGE                   **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!Kindly check & unblock the command as per the requirement!" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("!RLSMC:CELL=" + cell.name + ",SIMSG=1,MSGDIST=ON;" + eol);
				sb.append("!RLSMC:CELL=" + cell.name + ",SIMSG=7,MSGDIST=OFF;" + eol);
				sb.append("!RLSMC:CELL=" + cell.name + ",SIMSG=8,MSGDIST=OFF;" + eol);
				sb.append(eol);
			}
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**            BELOW PART IS ONLY NEEDED FOR UTRAN RELATIONS           **;" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!        ***** Define UTRAN measurement frequency information *****       !" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!Kindly check & execute the command as per the requirement!");
			sb.append(eol);
			try {
				for(GsmCell cell : duInfo.gsm2G.cellList) {
					String umfi = cell.umfi.replace(",", "&");
					if(cell.umfi.split(",").length > 8) {
						int length = cell.umfi.split(",").length;
						int i = 0;
						int j= i+8;
						while(length >0) {
							if(j > cell.umfi.split(",").length) {
								j = cell.umfi.split(",").length -1;
							}
							umfi = String.join("&",Arrays.copyOfRange(cell.umfi.split(","), i, j));
							sb.append("!RLUMC:CELL=" + cell.name + ", ADD, UMFI=" + umfi + ",LISTTYPE=IDLE;" + eol);
							i= j-1;
							j+=8;
							length -=8;
						}
					}
					else {
						sb.append("!RLUMC:CELL=" + cell.name + ", ADD, UMFI=" + umfi + ",LISTTYPE=IDLE;" + eol);
					}
					
				}
			}
			
			catch(Exception e) {
				Logger.logger.error("Error in umfi frequencies", e);
				Logger.getGmoLogger().printError("Error in umfi frequencies" + e.getMessage());
			}
			
			sb.append(eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!         ***** Add UTRAN data to System Information             *****    !" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append(eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLSUC:CELL=" + cell.name + ",FDDMRR=0,QSC=15,QSCI=0,QSI=7,SPRIO=NO,FDDQMIN=6,FDDQOFF=0;" + eol);
			}
			sb.append(eol);
			sb.append("!------------------------------------EOF--------------------------------------!" + eol);
			
			sb.append(eol);
			sb.append("!************************************************************************;" + eol
					+ "!         ***** Power savings data            *****    !" + eol
					+ "!************************************************************************;" + eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLSVC:CELL=" + cell.name + ",BTSPSHYST=4;" + eol);
			}
			sb.append(eol);
			sb.append("!************************************************************************;" + eol
					+ "!         ***** maximum channel data          *****    !" + eol
					+ "!************************************************************************;" + eol);
			for (GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLDRC:CELL=" + cell.name + ",CMDR=144;" + eol);
			}
			sb.append(eol);
			
//Excalibur_215
			sb.append("!************************************************************************;" + eol);
			sb.append("!         ***** EGPRS access on CCCH          *****    !" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("" + eol);
			for (GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLBDC:CELL=" + cell.name + ",CHGR=0,EACPREF=YES;" + eol);
			}
			
			sb.append("" + eol);
			sb.append("" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("!         ***** Lower limit of signal strength in MS          *****    !" + eol);
			sb.append("!************************************************************************;" + eol);
			sb.append("" + eol);
			for (GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLLOC:CELL=" + cell.name + ",MSRXMIN=101;" + eol);
			}
			
			sb.append("" + eol);

			sb.append("!------------------------------------EOF--------------------------------------!" + eol);
			
			
			sb.append("!************************************************************************;" + eol
					+ "!         ***** TNs can be configured with TCHs supporting EGPRS and GPRS         *****    !" + eol
					+ "!************************************************************************;" + eol);
			for (GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RLBDC:CELL=" + cell.name + ",TNBCCH=EGPRS;" + eol);
			}
			sb.append(eol);
			sb.append("!------------------------------------EOF--------------------------------------!" + eol);
			
			sb.append("!************************************************************************;" + eol);
			sb.append("!**                      DEFINITION OF TG                              **;" + eol);
			sb.append("!************************************************************************;" + eol);
			
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RXMOI:MO=RXSTG-" + cell.tg + ",RSITE=" + cell.rSite + ",SECTOR=" + cell.name + ";" + eol);
			}
			
			sb.append("!---------------------------------------------------------------!" + eol);
			sb.append("!                ***** CONNECT TG TO CELL *****                 !" + eol);
			sb.append("!---------------------------------------------------------------!" + eol);
			
			for(GsmCell cell : duInfo.gsm2G.cellList) {
				sb.append("RXTCI:MO=RXSTG-" + cell.tg + ", CELL=" + cell.name + ", CHGR=0;" + eol);
			}
			sb.append("!************************************************************************!" + eol);
			sb.append("!**                      DEFINITION OF DSCP                              **" + eol);
			sb.append("!************************************************************************!" + eol);
			for(GsmCell cell : duInfo.gsm2G.cellList) {
			sb.append("RXMOP:MO=RXSTG-" + cell.tg + ";" + eol
					+ "RXMOC:MO=RXSAT-" + cell.tg + ",SAPI=62,DSCPDL=0,DSCPUL=0;" + eol
					+ "RXMOC:MO=RXSAT-" + cell.tg + ",SAPI=0,DSCPDL=18,DSCPUL=18;" + eol
					+ "RXMOC:MO=RXSAT-" + cell.tg + ",SAPI=10,DSCPDL=18,DSCPUL=18;" + eol
					+ "RXMOC:MO=RXSAT-" + cell.tg + ",SAPI=11,DSCPDL=18,DSCPUL=18;" + eol
					+ "RXMOC:MO=RXSAT-" + cell.tg + ",SAPI=12,DSCPDL=18,DSCPUL=18;" + eol
					+ "RXMOP:MO=RXSTG-" + cell.tg + ";" + eol
					+ "RXESI:MO=RXSTG-" + cell.tg + ";" + eol
					+ "RXBLE:MO=RXSTG-" + cell.tg + ";" + eol);
			}
			sb.append("!****************************** EOF **********************************!");
			
			sb.append(eol + eol + eol + eol);
			
			FileUtil.writeToFile(sb, fileName);
		} catch (Exception e) {
			Logger.logger.error("generate generateBscCellData Scripts exception!", e);
			Logger.getGmoLogger().printError("Error while generating generateBscCellData!" + e.getMessage());
		}
		
	}

	private void generateNGSfor5GFirstNodeScripts(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			sb.append("lt all" + eol);
			sb.append("confb+" + eol);
			sb.append("gs+" + eol + eol + eol);

//			{	// TC_361
			String nodeType = (duInfo.isBBU || duInfo.nodeType.matches("BB.*") || duInfo.outputFormat.contentEquals("G2")) ? "BB" : duInfo.nodeType;
			sb.append(tmoCCR.generateGenericNodeNameBlock(duInfo.duName, nodeType));		// [10272020]
//			}
//			else {
//				sb.append(tmoCCR.generateGenericFingerPrintBlock(duInfo.duName));	// [05152020]
//			}

			ArrayList<String> lstSyncRiPortsToUse = new ArrayList<String>();
			for(String currSyncRiPortCandidateString : duInfo.syncRiPortCandidateList) {
				if(!currSyncRiPortCandidateString.endsWith("=D")) {
					lstSyncRiPortsToUse.add(currSyncRiPortCandidateString);
				}
			}

			sb.append("bl NodeGroupSyncMember=1" + eol);
			sb.append("set NodeGroupSyncMember=1 syncRiPortCandidate " + String.join(",", lstSyncRiPortsToUse) + eol);
			sb.append("deb NodeGroupSyncMember=1" + eol);

			sb.append(eol);

			sb.append("gs-" + eol);
			sb.append("confb-" + eol);

			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generateNGSfor5GFirstNodeScripts exception!", ex);
			Logger.getGmoLogger().printError("Error generating 5G NR600 NGS script for First node! " + ex.getMessage());
		}
	}

	// [eusxjas 08020219] TC_175
	private void generate5GNR600NodeGroupSyncMemberScriptForNGS(SiteCellObj duInfo, String lteDuName, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			sb.append("lt all" + eol);
			sb.append("confb+" + eol);
			sb.append("gs+" + eol + eol + eol);

//			{	// TC_361
			String nodeType = (duInfo.isBBU || duInfo.nodeType.matches("BB.*") || duInfo.outputFormat.contentEquals("G2")) ? "BB" : duInfo.nodeType;
			sb.append(tmoCCR.generateGenericNodeNameBlock(duInfo.duName, nodeType));		// [10272020]
//			}
//			else {
//				sb.append(tmoCCR.generateGenericFingerPrintBlock(duInfo.duName));	// [05152020]
//			}

			List<String> features = new ArrayList<>();
		    features.add("MixedModeRadioNr");
		    for(String feature:features) {
		    	String value = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("FeatureMap"), "name", feature , "keyId");	// For future compatibility, not currently used for 5G
		    	value = value.isEmpty() ? "CXC4012307" : value;
		    	sb.append("lset SystemFunctions=1,Lm=1,FeatureState=" + value + " featureState 1" + eol + eol);
		    }

			TreeMap<String, RfBranchObj> currRfBranchTreeMap = new TreeMap<String, RfBranchObj>();	// [08132019] TreeMap required to sort kget data

			Integer maxSupportSect = 9;		// [09112019] Added support for upto 9 sectors, was 3
			Integer count = 0;		// [08230219] Added count in case of sectors that don't start with 1, may start with 2
			for(Map.Entry<String, AntennaUnitGroupObj> kvp : duInfo.antennaUnitGroupMap.entrySet()) {
				AntennaUnitGroupObj currAugObj = kvp.getValue();
				RfBranchObj currRfBranch = null;
				count++;
				for(Map.Entry<String, RfBranchObj> kvpRfB : currAugObj.rfBranchMap.entrySet()) {
					// get only the first RfBranch, because you are only interested in getting the FieldReplaceableUnitId from the first RfBranch.
					// Also, down below where we are creating the RfBranches, we are assuming that we will always have 4 RfBranches with standard conventions for RfPort, AuPort.
					currRfBranch = kvpRfB.getValue();
					int secEquipFuncLastDigit = Integer.parseInt(kvpRfB.getValue().fieldReplaceableUnitId.substring(kvpRfB.getValue().fieldReplaceableUnitId.length()-2).replace("-", ""));		// [09112019] Updated to retrieve up to 2 digits
					if(secEquipFuncLastDigit > maxSupportSect && (count > maxSupportSect)) 	// [08142019 - eusxjas] Currently only 3 sectors is supported by software. If 4 sectors are found, then give a warning message
					{
						Logger.getGmoLogger().printWarning("5G software currently supports a maximum of " + maxSupportSect + " sectors for NGS! kget + RND shows " + secEquipFuncLastDigit + " sectors.");
						break;
					}
					currRfBranchTreeMap.put(currRfBranch.fieldReplaceableUnitId, currRfBranch);
					break;
				}
			}


			for(Map.Entry<String, RfBranchObj> kvp : currRfBranchTreeMap.entrySet()) {	// [081302019] Output based on sorted RND data
				sb.append("set FieldReplaceableUnit=" + kvp.getValue().fieldReplaceableUnitId + "$ isSharedWithExternalMe true" + eol);
			}

			sb.append(eol + "crn Transport=1,Synchronization=1,RadioEquipmentClock=1,NodeGroupSyncMember=1" + eol);
			sb.append("syncNodePriority 3" + eol);

			char [] arrRiPortNames = new char[] {' ', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'J'};		// [08232019] Added D in case of cellid 2,3,4 instead of 1,2,3, [09102019] Added E to J, skipping I
			count = 0;		// [09110219] Added count in case skipped sectors above 3

			int maxIndexUsed = 0;		// TC_212 [09172019]
			for(Map.Entry<String, RfBranchObj> kvp : currRfBranchTreeMap.entrySet()) {
				count++;
				int gUtranSectIdnum = Integer.parseInt(kvp.getKey().replaceAll(".*-", ""));		// Remove leading "6-"
				if(gUtranSectIdnum <= maxSupportSect) {
					maxIndexUsed = gUtranSectIdnum > 3 ? Integer.max(maxIndexUsed + 1, 4) : Integer.max(maxIndexUsed, gUtranSectIdnum);		// [09252019] In case sectors 1-3 are skipped, sectors 4+ will start from 4th index and next higher
					char riPortName = gUtranSectIdnum > 3 ? arrRiPortNames[maxIndexUsed] : arrRiPortNames[gUtranSectIdnum];	// [09112019] First 3 sectors should be A, B or C even if skipped sector, 4th sector and above should be in sequence D,E,F even if skipped sector (this is due to cabling done in advance)

					sb.append("syncRiPortCandidate Equipment=1,FieldReplaceableUnit=BB-01,RiPort=" + riPortName + eol);
				}
				else {
					Logger.getGmoLogger().printWarning("5G " + duInfo.duName + ", cellid " + gUtranSectIdnum + " is not mapped to a RiPort for syncRiPortCandidate.");
				}
			}

			sb.append("end" + eol + eol);
			sb.append("deb NodeGroupSyncMember=1" + eol + eol);
			sb.append("gs-" + eol);
			sb.append("confb-" + eol);

			FileUtil.writeToFile(sb, file);														 // [09172019] Changed to generate 5G NGS no matter what if L600 is existing or not, no regard to L600 radio type
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNR600NodeGroupSyncMemberScriptForNGS exception!", ex);
			Logger.getGmoLogger().printError("Error generating 5G NR600 NodeGroupSyncMember script for NGS! " + ex.getMessage());
		}
	}

	// [eusxjas 08020219] TC_175
	/**
	 * Function to generate LTE NGS script block for L600 split for 5G Carrier Add scope
	 * @return
	 */
	private void generateL600SplitLTENGSfor5GScriptBlock(String duName, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		StringBuilder sb = new StringBuilder();

		try
		{
			String l600DuName = CSVUtils.readDataFromCSVFile(CSVUtils.getKGETCSVFile("EUtranCellFDD"), "NodeMOKey", duName + "[\\d]*!.*", "freqBand", "71", "NodeMOKey");		// [08132019] For confirming duName in case it ends with a number or if 2 kgets exist (only one should have L600)
			l600DuName = l600DuName.isEmpty() ? duName : l600DuName.substring(0, l600DuName.indexOf("!"));									// Find duName from kget data that is delimited by !
			file = file.replace(duName, l600DuName);
			duName = l600DuName;

			String nodeType = "6630";
			nodeType = CSVUtils.readDataFromCSVFile(CSVUtils.getKGETCSVFile("FieldReplaceableUnit"), "NodeMOKey", duName + "[\\d]*!.*", "productData", ".*5216.*" , "productData");
			nodeType = nodeType.contains("5216") ? "5216" : "6630";
			file = file.replace("6630", nodeType);

			String l600Sectors = "3Sec";			// Default, 3 sectors, in file name
			String l600SectorsNew = "";
			ArrayList<String> l600EUtranCellFddArray = CSVUtils.readDataArrayFromCSVFile(CSVUtils.getKGETCSVFile("EUtranCellFDD"), "NodeMOKey", duName + "[\\d]*!.*", "freqBand", "71", "EUtranCellFDDId", false);		// duName with L600 usually does not have number at the end of duname but maybe a few cases in the network
			l600EUtranCellFddArray.sort(null);
			Integer l600CellCount = l600EUtranCellFddArray.size();
			for(String l600EUtranCellFdd : l600EUtranCellFddArray) {
				String cellSector = TMO_CommonUtil.getCellSectorFromCellName(l600EUtranCellFdd);
				String sectorName = tmoCCR.cellNumberToSectorNameHash.get(cellSector);
				l600SectorsNew = l600SectorsNew.isEmpty() ? sectorName : l600SectorsNew + "_" + sectorName;	// List sectors in cell name, when less than 3 sectors
			}

			l600SectorsNew = l600SectorsNew.isEmpty() || l600CellCount == 3 ? l600Sectors : l600SectorsNew;

			file = file.replace(l600Sectors, l600SectorsNew);
			Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
			
			sb.append("lt all" + eol);
			sb.append("confb+" + eol);
			sb.append("gs+" + eol + eol + eol);

//			{	// TC_361
			sb.append(tmoCCR.generateGenericNodeNameBlock(duName, nodeType));		// [10272020]
//			}
//			else {
//				sb.append(tmoCCR.generateGenericFingerPrintBlock(duName));	// [05152020]
//			}

			sb.append("//bls EUtranCellFDD=E" + eol + eol + eol);

			List<String> features = new ArrayList<>();
		    features.add("MixedMode");
		    for(String feature:features) {
		    	String value = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("FeatureMap"), "name", feature , "keyId");
		    	value = value.isEmpty() ? "CXC4011018" : value;
		    	sb.append("lset SystemFunctions=1,Lm=1,FeatureState=" + value + " featureState 1" + eol + eol);
		    }

		    // L600 Radios, Per LTE kget, find all string contains "productName = Radio 4449" and/or "productName = Radio 4478"
		    String l600Radios = "4449|4478";
			ArrayList<String> l600FieldReplaceableUnitArray = CSVUtils.readDataArrayFromCSVFile(CSVUtils.getKGETCSVFile("FieldReplaceableUnit"), "NodeMOKey", duName + "[\\d]*!.*", "productData", ".* (" + l600Radios + ") .*", "FieldReplaceableUnitId", false);
			ArrayList<String> l600RiLinkRiPortRefArray = new ArrayList<String>();		// [08282019] Moved/Added to here
			ArrayList<String> l600RiPortArray = new ArrayList<String>();				// [08282019] Moved to here
			Boolean newRiPort = false;													// [09172019] TC_212 Do not generate script if 4G node is already NGS, no changes in Riports
			ArrayList<String> unusedFieldReplaceableUnitArray = new ArrayList<String>();
			for(String l600FieldReplaceableUnit : l600FieldReplaceableUnitArray) {
				l600RiLinkRiPortRefArray = CSVUtils.readDataArrayFromCSVFile(CSVUtils.getKGETCSVFile("RiLink"), "NodeMOKey", duName + "!.*", "riPortRef2", ".*" + l600FieldReplaceableUnit + ",.*", "riPortRef1", false);		// Will need to search both riPortRef columns for L600 RRU
				if(l600RiLinkRiPortRefArray.isEmpty()) {
					l600RiLinkRiPortRefArray = CSVUtils.readDataArrayFromCSVFile(CSVUtils.getKGETCSVFile("RiLink"), "NodeMOKey", duName + "!.*", "riPortRef1", ".*" + l600FieldReplaceableUnit + ",.*", "riPortRef2", false);
				}
				if(!l600RiLinkRiPortRefArray.isEmpty()) {
					for (String l600RiPortRef : l600RiLinkRiPortRefArray) {
						String l600RiPort = l600RiPortRef.replaceAll(".*FieldReplaceableUnit", "FieldReplaceableUnit");	// Only need FieldReplaceableUnit, RiPort values
						if(!l600RiPort.isEmpty()) {
							if(l600RiPort.contains("XMU")) {		// [08092019] Added check to convert FieldReplaceableUnit=XMU, RiPort to standard RiPorts=A,B and C (no matter how many sectors/RRU in L600)
								if(l600RiPort.matches(".*RiPort=(13|14|15|16)") && !l600RiPortArray.contains("FieldReplaceableUnit=1,RiPort=A"))
									l600RiPortArray.add("FieldReplaceableUnit=1,RiPort=A");
								if(l600RiPort.matches(".*RiPort=(9|10|11|12)") && !l600RiPortArray.contains("FieldReplaceableUnit=1,RiPort=B"))
									l600RiPortArray.add("FieldReplaceableUnit=1,RiPort=B");
								if(l600RiPort.matches(".*RiPort=(4|5|6|7)") && !l600RiPortArray.contains("FieldReplaceableUnit=1,RiPort=C"))
									l600RiPortArray.add("FieldReplaceableUnit=1,RiPort=C");
							}
							else if(!l600RiPortArray.contains(l600RiPort)) {
								l600RiPortArray.add(l600RiPort);
							}
						}
						else {
							Logger.getGmoLogger().printError("Missing/Invalid L600 RiPort in kget for site: " + duName + ". Edit/check the script '" + file + "'.");
						}
					}
				}
				else {
					unusedFieldReplaceableUnitArray.add(l600FieldReplaceableUnit);		// RRU not tied to a Rilink, will be removed from another list
					Logger.getGmoLogger().printError("No RRU (" + l600FieldReplaceableUnit + ") found as riPortRef in kget for site: " + duName + ". Edit/check the script '" + file + "'.");
				}
			}
			for(String unusedFieldReplaceableUnit: unusedFieldReplaceableUnitArray) {
				l600FieldReplaceableUnitArray.remove(unusedFieldReplaceableUnit);		// Only used RRU will be included in the list
			}

			if(l600FieldReplaceableUnitArray.isEmpty()) {		// If LTE radios have not been upgraded, use default, give ERROR message for user but do  NOT ([09102019]) generate scripts
				if(l600CellCount > 0) {	// [09102019] Changed message if l600 requires 4G Carrier add scope 
					Logger.getGmoLogger().printError("L600 radios have not been upgraded (to Radio " + l600Radios + ") for site: " + duName + ". NGS scripts should be generated via 4G carrier add.");		// [09172019]
				}
				else {
					Logger.getGmoLogger().printError("No L600 found for site: " + duName + ". NGS scripts should be generated via 4G carrier add.");
				}
			}
			else if((l600FieldReplaceableUnitArray.size() < l600CellCount)) { 
				Integer notUpgradedCount = l600CellCount- l600FieldReplaceableUnitArray.size();
				String radioHaveHas = notUpgradedCount > 1 ? "radios have" : "radio has";
				Logger.getGmoLogger().printError(notUpgradedCount + ", L600 " + radioHaveHas + " not been upgraded (to Radio " + l600Radios + ") for site: " + duName + ". Edit/check the script '" + file + "'.");
			}

			Collections.sort(l600FieldReplaceableUnitArray);	// [08132019] Ada wants sequential output for consistent look for scripts between sites
			for(int i = 0; i < l600FieldReplaceableUnitArray.size() ; i++) {
				String l600FieldReplaceableUnit = l600FieldReplaceableUnitArray.get(i);
				
				if(l600FieldReplaceableUnit.contains("RRU-")) {
					sb.append("set FieldReplaceableUnit=" + l600FieldReplaceableUnit + "$ isSharedWithExternalMe true" + eol);
				}
				else {
					Logger.getGmoLogger().printError("L600 FieldReplaceableUnitId (" + l600FieldReplaceableUnit + ") is invalid for site: " + duName + ". Edit/check the script '" + file + "'.");
				}
			}

			String syncRiPortCandidateString = CSVUtils.readDataFromCSVFile(CSVUtils.getKGETCSVFile("NodeGroupSyncMember"), "NodeMOKey", duName + "!.*", "syncRiPortCandidate");	// TC_212 [09182019] MO exists only if NGS is active
			Collections.sort(l600RiPortArray);			// [08282019] Moved command to here
			if(!syncRiPortCandidateString.isEmpty()) {	// TC_212 [09252019]
				String syncRiPortCandidateRiPorts = "";

				for(String syncRiPortCandidate : syncRiPortCandidateString.split(";")) {					// Existing RiPorts in MO
					syncRiPortCandidate = syncRiPortCandidate.replaceAll(".*Equipment", "Equipment");		// Remove leading parent MO names
					syncRiPortCandidateRiPorts = syncRiPortCandidateRiPorts.concat(syncRiPortCandidate.isEmpty() ? "" : " " + syncRiPortCandidate);
				}

				for(String l600RiPort : l600RiPortArray) {													// New RiPorts to add in MO
					if(!syncRiPortCandidateRiPorts.contains(l600RiPort)) {									// Add only if not existing in MGS MO
						syncRiPortCandidateRiPorts = syncRiPortCandidateRiPorts.concat(l600RiPort.isEmpty() ? "" : " Equipment=1," + l600RiPort);
						newRiPort = true;																	// Generate script if new Riports need to be added to NGS, otherwise, don't create script
					}
				}

				if(!syncRiPortCandidateRiPorts.isEmpty()) {
					sb.append(eol + "bl NodeGroupSyncMember=1" + eol);
					sb.append("set NodeGroupSyncMember=1 syncRiPortCandidate" + syncRiPortCandidateRiPorts + eol);
				}

			}
			else {
				newRiPort = true;

				sb.append(eol + "crn Transport=1,Synchronization=1,RadioEquipmentClock=1,NodeGroupSyncMember=1" + eol);
				sb.append("syncNodePriority 1" + eol);

				for(String l600RiPort : l600RiPortArray) {
					sb.append("syncRiPortCandidate Equipment=1," + l600RiPort + eol);
				}
				sb.append("end" + eol + eol);
			}

			sb.append("deb NodeGroupSyncMember=1" + eol);
			sb.append("//deb EUtranCellFDD=E" + eol + eol);
			sb.append("gs-" + eol);
			sb.append("confb-" + eol);

			if(l600FieldReplaceableUnitArray.size() > 0 && newRiPort) { 	 // [09252019] Changed to generate 4G NGS here only if L600 radio type is 4449/4478 and L600 is not NGS already or is changing/added RiPort. Otherwise 4G NGS will be generated separately by MultiDu, 4G carrier add option
				FileUtil.writeToFile(sb, file);
			}
			else if(!newRiPort) {
				Logger.getGmoLogger().printTextWithTimeStamp("Required RiPorts already defined as syncRiPortCandidates. No NGS script necessary for LTE.");
			}
		}
		catch(Exception ex)
		{
			Logger.logger.error("generateL600SplitLTENGSfor5GScriptBlock exception!", ex);
			Logger.getGmoLogger().printError("Error generating L600 Split LTE NGS for 5G carrier add script! " + ex.getMessage());
		}
	}

 	private void generate5GNRSiteInstallXML(SiteCellObj duInfo, String file, String eolType)
 	{
  		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			String tnPort = "";
			
				if(duInfo.tmoDUInfo.getIsMidBandAnchorScopeWith6449Radio() || duInfo.nodeType.contains("6648") || duInfo.nodeType.contains("6651")) {	// [02052021] TC_384 updated for 6648
					//[09252020] - tnPort = TN_IDL_B will remain same for all markets
					tnPort = "TN_IDL_B";

				}else {
					tnPort = "TN_A";
				}
			
	 		sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
	 		sb.append("<RbsSiteInstallationFile xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:noNamespaceSchemaLocation=\"SiteInstallation.xsd\">" + eol);
	 		sb.append("  <Format revision=\"K\" />" + eol);
	 		if((duInfo.tmoDUInfo.isLowBandMMBBVariation || duInfo.tmoDUInfo.isMidBandTddMMBBVariation || duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode())
	 				&& (duInfo.is5G || duInfo.tmoDUInfo.isMMBBNode) && !duInfo.isNRNodeLive) {
	 			
	 			if (!duInfo.nodeType.contains("6648") && !duInfo.nodeType.contains("6651")) {		// [02052021] TC_384 updated for difference with 6648
	 				tnPort = "TN_A";
	 			} 
	 			
	 			sb.append("  <InstallationData tnPort=\"" + tnPort + "\" logicalName=\"" + duInfo.duName + "\" vlanId=\"" + duInfo.tmoDUInfo.gNodeBOamVlanId + "\">" + eol);
		 		sb.append("    <OamIpConfigurationData defaultRouter0=\"" + duInfo.tmoDUInfo.gNodeBOamDefaultRouter + "\" ipAddress=\"" + duInfo.tmoDUInfo.gNodeBoamIP + "\" subnetMask=\"" + duInfo.tmoDUInfo.gNodeBOamSubnetMask + "\" />" + eol);
	 		}
	 		else if (duInfo.tmoDUInfo.isIPSecConfiguration) {
	 			sb.append("  <InstallationData>" + eol);
	 		}
	 		else {
	 			
	 			sb.append("  <InstallationData tnPort=\"" + tnPort + "\" logicalName=\"" + duInfo.duName + "\" vlanId=\"" + duInfo.oamVlanId + "\">" + eol);
		 		sb.append("    <OamIpConfigurationData defaultRouter0=\"" + duInfo.oamDefaultRouter + "\" ipAddress=\"" + duInfo.oamIP + "\" subnetMask=\"" + duInfo.oamSubnetMask + "\" />" + eol);
	 		}
	 		if (duInfo.tmoDUInfo.isIPSecConfiguration) {
	 			sb.append("    <SmrsData>" + eol);
	 			sb.append("    </SmrsData>" + eol);
	 		}
	 		else {
	 			sb.append("    <SmrsData summaryFilePath=\"\" address=\"\" />" + eol);
	 		}
	 		sb.append("  </InstallationData>" + eol);
	 		if (duInfo.tmoDUInfo.isIPSecConfiguration && TMOConstants.tmoIPSecIRUConfiguration.matches("1_IRU")) {
	 			sb.append("          <UntrustedNetworkTemporaryConfigurationData>" + eol);
	 			sb.append("              <InnerIpConfigurationData>" + eol);
	 			sb.append("                <InnerDnsServer>" + eol);
	 			sb.append("                </InnerDnsServer>" + eol);
	 			sb.append("                <InnerNtpServer ipAddress=\"" + duInfo.tmoDUInfo.NTPServerAddress1 + "\">" + eol);
	 			sb.append("                </InnerNtpServer>" + eol);
	 			sb.append("            </InnerIpConfigurationData>" + eol);
	 			sb.append("        </UntrustedNetworkTemporaryConfigurationData>" + eol);
	 		}
	 		sb.append("</RbsSiteInstallationFile>" + eol);

	 		FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNRSiteInstallXML exception!", ex);
			Logger.getGmoLogger().printError("Error generating SiteInstallation script! " + ex.getMessage());
		}
 	}

 	// Deprecated
 	private void generate5GNRL19Q1NodeInfoXml(SiteCellObj duInfo, String file, String eolType)
 	{
 		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
	 		sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
	 		sb.append("<nodeInfo xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:noNamespaceSchemaLocation=\"NodeInfo.xsd\">" + eol);
	 		sb.append("  <name>" + duInfo.duName + "</name>" + eol);
	 		// [eshinai: 070319] Hard-coding nodeIdentifier because of CMCIQ sync issue causing an old version to be read from the CMCIQ instead of from the latest version.
	 		sb.append("  <nodeIdentifier>18.Q4-R8A20</nodeIdentifier>" + eol);
	 		sb.append("  <ipAddress>" + duInfo.oamIP + "</ipAddress>" + eol);
	 		sb.append("  <nodeType>5GRadioNode</nodeType>" + eol);
	 		sb.append("  <ossPrefix>" + duInfo.nodeInfoObj.ossPrefix + "</ossPrefix>" + eol);
	 		sb.append("  <timeZone>" + duInfo.pciSiteObj.timeZoneARNE + "</timeZone>" + eol);
	 		sb.append("  <autoIntegration>" + eol);
	 		sb.append("    <upgradePackageName>" + duInfo.pciSiteObj.upgradePackageName + "</upgradePackageName>" + eol);
	 		sb.append("  </autoIntegration>" + eol);
	 		if(duInfo.is5G && duInfo.isNR600){
		 		sb.append("  <supervision>" + eol);
				sb.append("  	<fm>disabled</fm>" + eol);
				sb.append("  	<pm>disabled</pm>" + eol);
				sb.append("  </supervision>" + eol);
	 		}
	 		sb.append("  <license>" + eol);
	 		sb.append("    <installLicense>true</installLicense>" + eol);
	 		sb.append("  </license>" + eol);
	 		sb.append("  <users>" + eol);
	 		sb.append("    <secureUser>" + eol);
	 		sb.append("      <name>prbs</name>" + eol);
	 		sb.append("      <password>prbs1234</password>" + eol);
	 		sb.append("    </secureUser>" + eol);
	 		sb.append("  </users>" + eol);
	 		sb.append("  <artifacts>" + eol);
	 		sb.append("    <siteBasic>" + duInfo.pciSiteObj.SiteBasicTemplateName + "</siteBasic>" + eol);
	 		sb.append("    <siteEquipment>" + duInfo.pciSiteObj.SiteEquipmentTemplateName + "</siteEquipment>" + eol);
	 		sb.append("    <siteInstallation>" + duInfo.pciSiteObj.SiteInstallationTemplateName + "</siteInstallation>" + eol);
	 		sb.append("    <configurations>" + eol);
	 		for (String nodeConfiguration : duInfo.nodeInfoObj.artifacts.configurations) {
				sb.append("      <nodeConfiguration>" + nodeConfiguration + "</nodeConfiguration>" + eol);
			}
	 		sb.append("    </configurations>" + eol);
	 		sb.append("  </artifacts>" + eol);
	 		sb.append("</nodeInfo>" + eol);
	 		FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNRNodeInfoXml exception!", ex);
			Logger.getGmoLogger().printError("Error generating NodeInfo script! " + ex.getMessage());
		}
 	}

 	private void generate5GNR600NodeInfoXml_MTR1923(SiteCellObj duInfo, String file, String eolType)
 	{
 		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<nodeInfo xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:noNamespaceSchemaLocation=\"NodeInfo.xsd\">" + eol);
			sb.append("  <name>" + duInfo.duName + "</name>" + eol);

			// #TC_216
			// check if this is a reconfig scope 2nd node
			if((duInfo.kgetCellFddIds.size() == 0) && (duInfo.rndCellFddIds.size() == 1) && !duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) {
				if (duInfo.nodeSupportObj.release.startsWith("R73")) {
					duInfo.nodeInfoObj.nodeIdentifier = "19.Q3-R41A26";			// [07212020]
				} else if (duInfo.nodeSupportObj.release.startsWith("R77")) {
					duInfo.nodeInfoObj.nodeIdentifier = "6537-213-642";			// [07212020]
				} else if (duInfo.nodeSupportObj.release.startsWith("R80")) {
					duInfo.nodeInfoObj.nodeIdentifier = "19.Q4-R49A04";			// [07212020]
				} else if (duInfo.nodeInfoObj.nodeIdentifier.isEmpty()) {		// [02042021] TC_381 Values are populated during data collection based on CM_CIQ
					Logger.getGmoLogger().printError("Error calculating nodeIdentifier for 5G NodeInfo script for non-Anchor Scope " + duInfo.duName);
				}
			} else if (duInfo.tmoDUInfo.isMidBandAnchorScope) {
				if (duInfo.nodeInfoObj.nodeIdentifier.isEmpty()) {		// [02042021] TC_381 Values are populated during data collection based on CM_CIQ
					Logger.getGmoLogger().printError("Error calculating nodeIdentifier for 5G NodeInfo script for MidBand Anchor Scope " + duInfo.duName);
				}
			} else if (duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) {
				if (duInfo.nodeInfoObj.nodeIdentifier.isEmpty()) {		// [02042021] TC_381 Values are populated during data collection based on CM_CIQ
					Logger.getGmoLogger().printError("Error calculating nodeIdentifier for 5G NodeInfo script for MidBand Anchor Scope With 6449 Radio " + duInfo.duName);
				}
				// this is not a reconfig scope. so continue using hard-coded nodeIdentifier.
				//duInfo.nodeInfoObj.nodeIdentifier = "20.Q3-R13A40";			// [10162020]
			} else if (duInfo.nodeInfoObj.nodeIdentifier.isEmpty()) {		// [02042021] TC_381 Values are populated during data collection based on CM_CIQ
				Logger.getGmoLogger().printError("Error calculating nodeIdentifier for 5G NodeInfo script for " + duInfo.duName);
			}

			if (duInfo.tmoDUInfo.isExcalibur4G5GFDD) {
				if(!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "L21.Q2")) {			// [01122022] EXCALIBUR_216
					duInfo.nodeInfoObj.nodeIdentifier = "20.Q4-R19A30";
					if (duInfo.softwareLevel.equals("L21Q1")) {
						duInfo.nodeInfoObj.nodeIdentifier = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("Excalibur_CM_CIQ_SW_LVL"), "Node", "MB LB MMBB FDD", "NodeIdentifier");
						duInfo.nodeInfoObj.upgradePackageName = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("Excalibur_CM_CIQ_SW_LVL"), "Node", "MB LB MMBB FDD", "UpgradePackageName");
						String upgradePackageName = duInfo.nodeInfoObj.upgradePackageName;
						upgradePackageName = duInfo.nodeInfoObj.upgradePackageName.replaceAll(".*RadioNode ", "");
						upgradePackageName = upgradePackageName.replaceAll(" [12]\\d\\.Q[1234]$", "");
						duInfo.pciSiteObj.upgradePackageId = upgradePackageName.replaceAll(" ", "_");
						duInfo.pciSiteObj.upgradePackageId = duInfo.pciSiteObj.upgradePackageId.replaceAll("/", "_");
						duInfo.pciSiteObj.release = duInfo.pciSiteObj.upgradePackageId.split("[\\s_-]")[2]; // [07212020] Added space for Id pulled from CM_CIQ
					}
				}
			}
			if( duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
				if(!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "L21.Q2") ) {			// [01122022] EXCALIBUR_216
					duInfo.nodeInfoObj.nodeIdentifier =  "20.Q4-R19A30";

					if(duInfo.softwareLevel.equals("L21Q1")) {
						duInfo.nodeInfoObj.nodeIdentifier = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("Excalibur_CM_CIQ_SW_LVL"), "Node", "MB MMBB TDD", "NodeIdentifier");
						duInfo.nodeInfoObj.upgradePackageName = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("Excalibur_CM_CIQ_SW_LVL"), "Node", "MB MMBB TDD", "UpgradePackageName");
						String upgradePackageName = duInfo.nodeInfoObj.upgradePackageName;
						upgradePackageName = duInfo.nodeInfoObj.upgradePackageName.replaceAll(".*RadioNode ", "");
						upgradePackageName = upgradePackageName.replaceAll(" [12]\\d\\.Q[1234]$", "");
						duInfo.pciSiteObj.upgradePackageId =  upgradePackageName.replaceAll(" ", "_");
						duInfo.pciSiteObj.upgradePackageId = duInfo.pciSiteObj.upgradePackageId .replaceAll("/","_");
						duInfo.pciSiteObj.release = duInfo.pciSiteObj.upgradePackageId.split("[\\s_-]")[2];	// [07212020] Added space for Id pulled from CM_CIQ
					}
				}
			}
			if (!duInfo.nodeInfoObj.nodeIdentifier.isEmpty()) {	// [07212020]
				sb.append("  <nodeIdentifier>" + duInfo.nodeInfoObj.nodeIdentifier + "</nodeIdentifier>" + eol);
			}

			sb.append("  <ipAddress>" + duInfo.oamIP + "</ipAddress>" + eol);
			sb.append("  <nodeType>RadioNode</nodeType>" + eol);
			if (duInfo.tmoDUInfo.isIPSecConfiguration) {
				sb.append("  <hardwareSerialNumber>" + duInfo.tmoDUInfo.hardwareSerialNumber + "</hardwareSerialNumber>" + eol);
			}
			sb.append("  <ossPrefix>" + duInfo.nodeInfoObj.ossPrefix + "</ossPrefix>" + eol);
			sb.append("  <timeZone>" + duInfo.pciSiteObj.timeZoneARNE + "</timeZone>" + eol);
			sb.append("  <autoIntegration>" + eol);

			// #TC_216
			if ((duInfo.kgetCellFddIds.size() == 0) && (duInfo.rndCellFddIds.size() == 1) && !duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) {
				if(duInfo.nodeSupportObj.release.startsWith("R73")) {
					duInfo.nodeInfoObj.upgradePackageName = "RadioNode CXP9024418/6 " + duInfo.nodeSupportObj.release + " 19.Q3";						 // [07212020]
					duInfo.nodeInfoObj.softwareLevel = "19Q3";
				} else if (duInfo.nodeSupportObj.release.startsWith("R77")) {
					duInfo.nodeInfoObj.upgradePackageName = "RadioNode CXP9024418/6 " + duInfo.nodeSupportObj.release + " 19.Q4";						 // [07212020]
					duInfo.nodeInfoObj.softwareLevel = "19Q4";
				} else if (duInfo.nodeSupportObj.release.startsWith("R80")) {
					duInfo.nodeInfoObj.upgradePackageName = "RadioNode CXP9024418/6 " + duInfo.nodeSupportObj.release + " 19.Q4";						 // [07212020]
					duInfo.nodeInfoObj.softwareLevel = "19Q4";
				} else if (duInfo.nodeInfoObj.upgradePackageName.isEmpty() || duInfo.nodeInfoObj.softwareLevel.isEmpty()) {		// [02042021] TC_381 Values are populated during data collection based on CM_CIQ
					Logger.getGmoLogger().printError("Error calculating upgradePackageName, softwareLevel for 5G NodeInfo script for non-Anchor Scope " + duInfo.duName);
				}
			} else if (duInfo.tmoDUInfo.isMidBandAnchorScope) {
				if (duInfo.nodeInfoObj.upgradePackageName.isEmpty() || duInfo.nodeInfoObj.softwareLevel.isEmpty()) {		// [02042021] TC_381 Values are populated during data collection based on CM_CIQ
					Logger.getGmoLogger().printError("Error calculating upgradePackageName, softwareLevel for 5G NodeInfo script for MidBand Anchor Scope " + duInfo.duName);
				}
			} else if(duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) {
				if (duInfo.nodeInfoObj.upgradePackageName.isEmpty() || duInfo.nodeInfoObj.softwareLevel.isEmpty()) {		// [02042021] TC_381 Values are populated during data collection based on CM_CIQ
					Logger.getGmoLogger().printError("Error calculating upgradePackageName, softwareLevel for 5G NodeInfo script for MidBand Anchor Scope With 6449 Radio " + duInfo.duName);
				}
			} else if (duInfo.nodeInfoObj.upgradePackageName.isEmpty() || duInfo.nodeInfoObj.softwareLevel.isEmpty()) {		// [02042021] TC_381 Values are populated during data collection based on CM_CIQ
				Logger.getGmoLogger().printError("Error calculating upgradePackageName, softwareLevel for 5G NodeInfo script for " + duInfo.duName);
			}


			if (!duInfo.nodeInfoObj.upgradePackageName.isEmpty()) {	// [07212020]
				sb.append("    <upgradePackageName>" + duInfo.nodeInfoObj.upgradePackageName + "</upgradePackageName>" + eol);
			}
			sb.append("  </autoIntegration>" + eol);
			sb.append("  <users>" + eol);
			sb.append("    <secureUser>" + eol);
			sb.append("      <name>prbs</name>" + eol);
			sb.append("      <password>prbs1234</password>" + eol);
			sb.append("    </secureUser>" + eol);
			sb.append("  </users>" + eol);
			sb.append("  <license>" + eol);
			sb.append("    <installLicense>true</installLicense>" + eol);
			//[ezrxxsu - 10312020]
			if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || duInfo.tmoDUInfo.isMidBandTddMMBBVariation) {
				String nodeName = (!duInfo.pciSiteObj.fingerPrint.isEmpty())? duInfo.pciSiteObj.fingerPrint : duInfo.duName;
				sb.append("    <fingerprint>" + nodeName + "</fingerprint>" + eol);
			}
			sb.append("  </license>" + eol);
			sb.append("  <artifacts>" + eol);
			sb.append("    <siteBasic>" + duInfo.pciSiteObj.SiteBasicTemplateName + "</siteBasic>" + eol);
	 		sb.append("    <siteEquipment>" + duInfo.pciSiteObj.SiteEquipmentTemplateName + "</siteEquipment>" + eol);
	 		sb.append("    <siteInstallation>" + duInfo.pciSiteObj.SiteInstallationTemplateName + "</siteInstallation>" + eol);
	 		sb.append("    <configurations>" + eol);
	 		for (String nodeConfiguration : duInfo.nodeInfoObj.artifacts.configurations) {
				sb.append("      <nodeConfiguration>" + nodeConfiguration + "</nodeConfiguration>" + eol);
			}
	 		sb.append("    </configurations>" + eol);
			sb.append("  </artifacts>" + eol);
			sb.append("</nodeInfo>" + eol);

			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNRNodeInfoXml exception!", ex);
			Logger.getGmoLogger().printError("Error generating NodeInfo script! " + ex.getMessage());
		}
 	}
 
 	// Deprecated
 	@Deprecated
	private void generate5GNRSiteEquipmentNetConf_test(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<hello xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <capabilities>" + eol);
			sb.append("    <capability>urn:ietf:params:netconf:base:1.0</capability>" + eol);
			sb.append("  </capabilities>" + eol);
			sb.append("</hello>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"1\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <edit-config>" + eol);
			sb.append("    <target>" + eol);
			sb.append("      <running />" + eol);
			sb.append("    </target>" + eol);
			sb.append("    <config xmlns:xc=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("      <ManagedElement xmlns=\"urn:com:ericsson:ecim:ComTop\">" + eol);
			sb.append("        <managedElementId>1</managedElementId>" + eol);
			sb.append("        <userLabel>" + duInfo.duName + "</userLabel>" + eol);
			sb.append("        <Equipment xmlns=\"urn:com:ericsson:ecim:ReqEquipment\">" + eol);
			sb.append("          <equipmentId>1</equipmentId>" + eol);
			sb.append("          <Cabinet xmlns=\"urn:com:ericsson:ecim:ReqCabinet\">" + eol);
			sb.append("            <cabinetId>1</cabinetId>" + eol);
			sb.append("            <climateSystem>STANDARD</climateSystem>" + eol);
			sb.append("          </Cabinet>" + eol);
			sb.append("          <EcBus xmlns=\"urn:com:ericsson:ecim:ReqEcBus\">" + eol);
			sb.append("            <ecBusId>1</ecBusId>" + eol);
			sb.append("            <ecBusConnectorRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01</ecBusConnectorRef>" + eol);
			sb.append("          </EcBus>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>BB-01</fieldReplaceableUnitId>" + eol);
			sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            <EcPort xmlns=\"urn:com:ericsson:ecim:ReqEcPort\">" + eol);
			sb.append("              <ecPortId>1</ecPortId>" + eol);
			sb.append("              <hubPosition>A6</hubPosition>" + eol);
			sb.append("              <ecBusRef>ManagedElement=1,Equipment=1,EcBus=1</ecBusRef>" + eol);
			sb.append("            </EcPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>A</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>B</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>C</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>D</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>E</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>F</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>G</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>H</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>J</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>K</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>L</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>M</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>N</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>P</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>Q</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			if(duInfo.isNR600)
			{
				// [eshinai:072619]  hard-code 3 AntennaUnitGroups for this script for now based on discussion with Ada today
				AntennaUnitGroupObj augObj = duInfo.antennaUnitGroupMap.get(duInfo.duName);
				augObj = new AntennaUnitGroupObj();
				// for NR600, we need 3 FRUs.
				RfBranchObj rfBranchObj = new RfBranchObj();
				rfBranchObj.fieldReplaceableUnitId = "6-01";
				augObj.rfBranchMap.put("1", rfBranchObj);

				rfBranchObj = new RfBranchObj();
				rfBranchObj.fieldReplaceableUnitId = "6-02";
				augObj.rfBranchMap.put("2", rfBranchObj);

				rfBranchObj = new RfBranchObj();
				rfBranchObj.fieldReplaceableUnitId = "6-03";
				augObj.rfBranchMap.put("3", rfBranchObj);

				duInfo.antennaUnitGroupMap.put("1", augObj);

				for(int i=1; i<=3 ; i++)
				{
					sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
					sb.append("            <fieldReplaceableUnitId>6-0" + i + "</fieldReplaceableUnitId>" + eol);
					sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
					sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
					sb.append("              <rfPortId>A</rfPortId>" + eol);
					sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
					sb.append("            </RfPort>" + eol);
					sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
					sb.append("              <rfPortId>B</rfPortId>" + eol);
					sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
					sb.append("            </RfPort>" + eol);
					sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
					sb.append("              <rfPortId>C</rfPortId>" + eol);
					sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
					sb.append("            </RfPort>" + eol);
					sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
					sb.append("              <rfPortId>D</rfPortId>" + eol);
					sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
					sb.append("            </RfPort>" + eol);
					sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
					sb.append("              <rfPortId>R</rfPortId>" + eol);
					sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
					sb.append("            </RfPort>" + eol);
					sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
					sb.append("              <riPortId>DATA_1</riPortId>" + eol);
					sb.append("            </RiPort>" + eol);
					sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
					sb.append("              <riPortId>DATA_2</riPortId>" + eol);
					sb.append("            </RiPort>" + eol);
					sb.append("          </FieldReplaceableUnit>" + eol);
				}
			}
			else if(duInfo.isMmWave)
			{
				for (Map.Entry<String, AntennaUnitGroupObj> augEntry : duInfo.antennaUnitGroupMap.entrySet()) {
					AntennaUnitGroupObj antennaUnitGroupObj = augEntry.getValue();
					for (Map.Entry<String, RfBranchObj> rfBranchEntry : antennaUnitGroupObj.rfBranchMap.entrySet()) {
						RfBranchObj rfBranchObj = rfBranchEntry.getValue();
						sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
						sb.append("            <fieldReplaceableUnitId>" + rfBranchObj.fieldReplaceableUnitId + "</fieldReplaceableUnitId>" + eol);
						sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
						sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
						sb.append("              <riPortId>DATA_1</riPortId>" + eol);
						sb.append("            </RiPort>" + eol);
						sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
						sb.append("              <riPortId>DATA_2</riPortId>" + eol);
						sb.append("            </RiPort>" + eol);
						sb.append("            <Transceiver xmlns=\"urn:com:ericsson:ecim:ReqTransceiver\">" + eol);
						sb.append("              <transceiverId>1</transceiverId>" + eol);
						sb.append("            </Transceiver>" + eol);
						sb.append("          </FieldReplaceableUnit>" + eol);
					}
				}
			}

			if(duInfo.isMmWave)
			{	
				for (Map.Entry<String, AntennaUnitGroupObj> augEntry : duInfo.antennaUnitGroupMap.entrySet()) {
					AntennaUnitGroupObj antennaUnitGroupObj = augEntry.getValue();
					for (Map.Entry<String, RfBranchObj> rfBranchEntry : antennaUnitGroupObj.rfBranchMap.entrySet()) {
						RfBranchObj rfBranchObj = rfBranchEntry.getValue();
						sb.append("          <RiLink xmlns=\"urn:com:ericsson:ecim:ReqRiLink\">" + eol);
						sb.append("            <riLinkId>BB-01-A-" + rfBranchObj.fieldReplaceableUnitId + "-Data1</riLinkId>" + eol);
						sb.append("            <riPortRef1>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01,RiPort=A</riPortRef1>" + eol);
						sb.append("            <riPortRef2>ManagedElement=1,Equipment=1,FieldReplaceableUnit=" + rfBranchObj.fieldReplaceableUnitId + ",RiPort=DATA_1</riPortRef2>" + eol);
						sb.append("          </RiLink>" + eol);
						sb.append("          <RiLink xmlns=\"urn:com:ericsson:ecim:ReqRiLink\">" + eol);
						sb.append("            <riLinkId>BB-01-B-" + rfBranchObj.fieldReplaceableUnitId + "-Data2</riLinkId>" + eol);
						sb.append("            <riPortRef1>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01,RiPort=B</riPortRef1>" + eol);
						sb.append("            <riPortRef2>ManagedElement=1,Equipment=1,FieldReplaceableUnit=" + rfBranchObj.fieldReplaceableUnitId + ",RiPort=DATA_2</riPortRef2>" + eol);
						sb.append("          </RiLink>" + eol);
						
					}
				}
			}
			sb.append("        </Equipment>" + eol);
			sb.append("        <EquipmentSupportFunction xmlns=\"urn:com:ericsson:ecim:ResEquipmentSupportFunction\">" + eol);
			sb.append("          <equipmentSupportFunctionId>1</equipmentSupportFunctionId>" + eol);
			sb.append("          <supportSystemControl>true</supportSystemControl>" + eol);
			sb.append("          <Climate xmlns=\"urn:com:ericsson:ecim:ResClimate\">" + eol);
			sb.append("            <climateId>1</climateId>" + eol);
			sb.append("            <controlDomainRef>ManagedElement=1,Equipment=1,Cabinet=1</controlDomainRef>" + eol);
			sb.append("            <climateControlMode>NORMAL</climateControlMode>" + eol);
			sb.append("          </Climate>" + eol);
			sb.append("        </EquipmentSupportFunction>" + eol);
			sb.append("        <NodeSupport xmlns=\"urn:com:ericsson:ecim:RmeSupport\">" + eol);
			sb.append("          <nodeSupportId>1</nodeSupportId>" + eol);
			sb.append("          <MpClusterHandling xmlns=\"urn:com:ericsson:ecim:RmeMpClusterHandling\">" + eol);
			sb.append("            <mpClusterHandlingId>1</mpClusterHandlingId>" + eol);
			sb.append("            <primaryCoreRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01</primaryCoreRef>" + eol);
			sb.append("          </MpClusterHandling>" + eol);

			if(duInfo.isMmWave)
			{	
				for (Map.Entry<String, AntennaUnitGroupObj> augEntry : duInfo.antennaUnitGroupMap.entrySet()) {
					AntennaUnitGroupObj antennaUnitGroupObj = augEntry.getValue();
					for (Map.Entry<String, RfBranchObj> rfBranchEntry : antennaUnitGroupObj.rfBranchMap.entrySet()) {
						RfBranchObj rfBranchObj = rfBranchEntry.getValue();
						sb.append("          <SectorEquipmentFunction xmlns=\"urn:com:ericsson:ecim:RmeSectorEquipmentFunction\">" + eol);
						sb.append("            <sectorEquipmentFunctionId>" + rfBranchObj.fieldReplaceableUnitId + "</sectorEquipmentFunctionId>" + eol);
						sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
						sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=" + rfBranchObj.fieldReplaceableUnitId + ",Transceiver=1</rfBranchRef>" + eol);
						sb.append("          </SectorEquipmentFunction>" + eol);
					}
				}
			}
			sb.append("        </NodeSupport>" + eol);
			sb.append("      </ManagedElement>" + eol);
			sb.append("    </config>" + eol);
			sb.append("  </edit-config>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"Closing\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <close-session></close-session>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);

			FileUtil.writeToFile(sb, file);

		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNRSiteEquipmentNetConf_test exception!", ex);
			Logger.getGmoLogger().printError("Error generating SiteEquipment script! " + ex.getMessage());
		}
	}

	private void generate5GNRSiteEquipmentNetConf(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();
		String fieldReplaceableUnitId = duInfo.tmoDUInfo.isIPSecConfiguration ? "1" : "BB-01";
		String supportSystemControl = duInfo.tmoDUInfo.isIPSecConfiguration ? "false" : "true";
		String siteAddress = duInfo.siteAddress != null ? duInfo.siteAddress.replaceAll(",", "") : "";

		try
		{
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<hello xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <capabilities>" + eol);
			sb.append("    <capability>urn:ietf:params:netconf:base:1.0</capability>" + eol);
			sb.append("  </capabilities>" + eol);
			sb.append("</hello>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"1\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <edit-config>" + eol);
			sb.append("    <target>" + eol);
			sb.append("      <running />" + eol);
			sb.append("    </target>" + eol);
			sb.append("    <config xmlns:xc=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("      <ManagedElement xmlns=\"urn:com:ericsson:ecim:ComTop\">" + eol);
			sb.append("        <managedElementId>1</managedElementId>" + eol);
			
			if (duInfo.tmoDUInfo.isIPSecConfiguration && !hasExcaliburSmallCells) {
				sb.append("         <siteLocation>" + siteAddress + "</siteLocation>" + eol);
			}
			sb.append("        <userLabel>" + duInfo.duName + "</userLabel>" + eol);
			sb.append("        <Equipment xmlns=\"urn:com:ericsson:ecim:ReqEquipment\">" + eol);
			sb.append("          <equipmentId>1</equipmentId>" + eol);
			sb.append("          <Cabinet xmlns=\"urn:com:ericsson:ecim:ReqCabinet\">" + eol);
			sb.append("            <cabinetId>1</cabinetId>" + eol);
			
			if ((duInfo.nodeType.contains("6648") || duInfo.nodeType.contains("6651")) && duInfo.tmoDUInfo.isExcalibur4G5GFDD) {
					sb.append("            <climateSystem>EXTENDED</climateSystem>" + eol);
			} else {
					sb.append("            <climateSystem>STANDARD</climateSystem>" + eol);
			}
			
			sb.append("          </Cabinet>" + eol);
			sb.append("          <EcBus xmlns=\"urn:com:ericsson:ecim:ReqEcBus\">" + eol);
			sb.append("            <ecBusId>1</ecBusId>" + eol);
			sb.append("            <ecBusConnectorRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=" + fieldReplaceableUnitId + "</ecBusConnectorRef>" + eol);
			sb.append("          </EcBus>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>" + fieldReplaceableUnitId + "</fieldReplaceableUnitId>" + eol);
			sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
			
				if (!duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.nodeType.contains("6648") && !duInfo.nodeType.contains("6651") && !hasExcaliburSmallCells) { // [02052021] TC_384 updated for 6648
					sb.append("            <EcPort xmlns=\"urn:com:ericsson:ecim:ReqEcPort\">" + eol);
					sb.append("              <ecPortId>1</ecPortId>" + eol);
					sb.append("              <hubPosition>A6</hubPosition>" + eol);
					sb.append("              <ecBusRef>ManagedElement=1,Equipment=1,EcBus=1</ecBusRef>" + eol);
					sb.append("            </EcPort>" + eol);
				}
			
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>A</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>B</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>C</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>D</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>E</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>F</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>G</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>H</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>J</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>K</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>L</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>M</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			
				if(!duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.nodeType.contains("6648") && !duInfo.nodeType.contains("6651") ) {	// [02052021] TC_384 updated for 6648
					sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
					sb.append("              <riPortId>N</riPortId>" + eol);
					sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
					sb.append("            </RiPort>" + eol);
					sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
					sb.append("              <riPortId>P</riPortId>" + eol);
					sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
					sb.append("            </RiPort>" + eol);
					sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
					sb.append("              <riPortId>Q</riPortId>" + eol);
					sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
					sb.append("            </RiPort>" + eol);
				}
			
			
			if (duInfo.tmoDUInfo.isIPSecConfiguration && !hasExcaliburSmallCells) {
				sb.append("            <SyncPort xmlns=\"urn:com:ericsson:ecim:ReqSyncPort\">" + eol);
				sb.append("              <syncPortId>1</syncPortId>" + eol);
				sb.append("            </SyncPort>" + eol);
			}
			sb.append("          </FieldReplaceableUnit>" + eol);
			
			if(hasExcaliburSmallCells) {
				sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
				sb.append("            <fieldReplaceableUnitId>25-01</fieldReplaceableUnitId>" + eol);
				sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
				sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
				sb.append("              <rfPortId>A</rfPortId>" + eol);
				sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
				sb.append("            </RfPort>" + eol);
				sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
				sb.append("              <rfPortId>B</rfPortId>" + eol);
				sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
				sb.append("            </RfPort>" + eol);
				sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
				sb.append("              <rfPortId>C</rfPortId>" + eol);
				sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
				sb.append("            </RfPort>" + eol);
				sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
				sb.append("              <rfPortId>D</rfPortId>" + eol);
				sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
				sb.append("            </RfPort>" + eol);
				sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
				sb.append("              <rfPortId>R</rfPortId>" + eol);
				sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
				sb.append("            </RfPort>" + eol);
				sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
				sb.append("              <riPortId>DATA_1</riPortId>" + eol);
				sb.append("            </RiPort>" + eol);
				sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
				sb.append("              <riPortId>DATA_2</riPortId>" + eol);
				sb.append("            </RiPort>" + eol);
				sb.append("          </FieldReplaceableUnit>" + eol);
			}
			
			boolean blnConditionOne = (duInfo.isNR600 || duInfo.tmoDUInfo.isLowBandMMBBVariation || duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode()) && !hasExcaliburSmallCells;
			blnConditionOne = duInfo.tmoDUInfo.triggerForTDDMMBBRRU8863Configuration ? false : blnConditionOne;
			boolean blnConditionTwo = duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || duInfo.tmoDUInfo.isMidBandTddMMBBVariation || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope());
			blnConditionTwo = duInfo.tmoDUInfo.triggerForTDDMMBBRRU8863Configuration ? false : blnConditionTwo;
			boolean blnConditionThree = duInfo.tmoDUInfo.triggerForTDDMMBBRRU8863Configuration ? true : false;
			if(blnConditionOne)
			{
				// radio MOs
				List<String> lstFruIdsToUse = duInfo.rndFieldReplaceableUnitIds5g;
				if(lstFruIdsToUse == null || lstFruIdsToUse.size() == 0) {
					lstFruIdsToUse = duInfo.kgetFieldReplaceableUnitIds5g;
				}

				if((lstFruIdsToUse == null || lstFruIdsToUse.size() == 0) && !duInfo.tmoDUInfo.isExcaliburConfig7) {
					lstFruIdsToUse = new ArrayList<String>();
					lstFruIdsToUse.add("6-01");
					lstFruIdsToUse.add("6-02");
					lstFruIdsToUse.add("6-03");
				}
				
				if((lstFruIdsToUse != null && lstFruIdsToUse.size()>0) && duInfo.tmoDUInfo.isExcaliburConfig7 && !duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
					lstFruIdsToUse = new ArrayList<String>();
				}

				if(lstFruIdsToUse != null) {
					for(String strCurrFruId : lstFruIdsToUse) {
						sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
						sb.append("            <fieldReplaceableUnitId>" + strCurrFruId + "</fieldReplaceableUnitId>" + eol);
						sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
						sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
						sb.append("              <rfPortId>A</rfPortId>" + eol);
						sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
						sb.append("            </RfPort>" + eol);
						sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
						sb.append("              <rfPortId>B</rfPortId>" + eol);
						sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
						sb.append("            </RfPort>" + eol);
						sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
						sb.append("              <rfPortId>C</rfPortId>" + eol);
						sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
						sb.append("            </RfPort>" + eol);
						sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
						sb.append("              <rfPortId>D</rfPortId>" + eol);
						sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
						sb.append("            </RfPort>" + eol);
						sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
						sb.append("              <rfPortId>R</rfPortId>" + eol);
						sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
						sb.append("            </RfPort>" + eol);
						sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
						sb.append("              <riPortId>DATA_1</riPortId>" + eol);
						sb.append("            </RiPort>" + eol);
						sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
						sb.append("              <riPortId>DATA_2</riPortId>" + eol);
						sb.append("            </RiPort>" + eol);
						sb.append("          </FieldReplaceableUnit>" + eol);
					}
				}
			}
//			else if(duInfo.isMmWave)  //TMO_202 - removing to keep a standard 
//			{
//				for(String strCurrFruId : duInfo.rndFieldReplaceableUnitIds5g) {
//					sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
//					sb.append("            <fieldReplaceableUnitId>" + strCurrFruId + "</fieldReplaceableUnitId>" + eol);
//					sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
//					sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
//					sb.append("              <riPortId>DATA_1</riPortId>" + eol);
//					sb.append("            </RiPort>" + eol);
//					sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
//					sb.append("              <riPortId>DATA_2</riPortId>" + eol);
//					sb.append("            </RiPort>" + eol);
//					sb.append("            <Transceiver xmlns=\"urn:com:ericsson:ecim:ReqTransceiver\">" + eol);
//					sb.append("              <transceiverId>1</transceiverId>" + eol);
//					sb.append("            </Transceiver>" + eol);
//					sb.append("          </FieldReplaceableUnit>" + eol);
//				}
//
//			}
			
			else if(blnConditionTwo) {
				List<String> lstFruIdsToUse = duInfo.rndFieldReplaceableUnitIds5g;
				if(lstFruIdsToUse == null || lstFruIdsToUse.size() == 0) {
					lstFruIdsToUse = duInfo.kgetFieldReplaceableUnitIds5g;
				}

				if(lstFruIdsToUse == null || lstFruIdsToUse.size() == 0) {
					lstFruIdsToUse = new ArrayList<String>();
					lstFruIdsToUse.add("25-01");
					lstFruIdsToUse.add("25-02");
					lstFruIdsToUse.add("25-03");
				}
				if(duInfo.isMmWave ) //tmo_202
				{
					
				}
				else
				for(String strCurrFruId : lstFruIdsToUse) {
					sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
					sb.append("            <fieldReplaceableUnitId>" + strCurrFruId + "</fieldReplaceableUnitId>" + eol);
					sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
					sb.append("            <isSharedWithExternalMe>true</isSharedWithExternalMe>" + eol);
					sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
					sb.append("              <riPortId>DATA_1</riPortId>" + eol);
					sb.append("            </RiPort>" + eol);
					sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
					sb.append("              <riPortId>DATA_2</riPortId>" + eol);
					sb.append("            </RiPort>" + eol);
					sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
					sb.append("              <riPortId>DATA_3</riPortId>" + eol);
					sb.append("            </RiPort>" + eol);
					if(duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || duInfo.tmoDUInfo.isMidBandTddMMBBVariation || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
						sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
						sb.append("              <riPortId>DATA_4</riPortId>" + eol);
						sb.append("            </RiPort>" + eol);
					}
					sb.append("            <Transceiver xmlns=\"urn:com:ericsson:ecim:ReqTransceiver\">" + eol);
					sb.append("              <transceiverId>1</transceiverId>" + eol);
					sb.append("            </Transceiver>" + eol);
					sb.append("          </FieldReplaceableUnit>" + eol);
				}
			}
			//GMO_TMO-188 RRU_8863_B41_N41_Update
			else if (blnConditionThree) {
				// radio MOs
				List<String> lstFruIdsToUse = duInfo.rndFieldReplaceableUnitIds5g;
				if(lstFruIdsToUse == null || lstFruIdsToUse.size() == 0) {
					lstFruIdsToUse = duInfo.kgetFieldReplaceableUnitIds5g;
				}
				if(lstFruIdsToUse != null) {
					for(String strCurrFruId : lstFruIdsToUse) {
						// GMO_TMO-188
						SiteCellObj cellInfo = tmoDC.getCellInfoAugId(duInfo, strCurrFruId);
						String rfPortArray = cellInfo.tmoCellInfo.rfPortIdHWTable;
						sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
						sb.append("            <fieldReplaceableUnitId>" + strCurrFruId + "</fieldReplaceableUnitId>" + eol);
						sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
						for (String rfPortId:rfPortArray.split("-")) {
							sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
							sb.append("              <rfPortId>" + rfPortId + "</rfPortId>" + eol);
							sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
							sb.append("            </RfPort>" + eol);
						}
						sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
						sb.append("              <riPortId>DATA_1</riPortId>" + eol);
						sb.append("            </RiPort>" + eol);
						sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
						sb.append("              <riPortId>DATA_2</riPortId>" + eol);
						sb.append("            </RiPort>" + eol);
						sb.append("          </FieldReplaceableUnit>" + eol);
					}
				}
			}

//			if(duInfo.isMmWave) //TMO_202 - removing to keep a standard 
//			{
//				for(String strCurrFruId : duInfo.rndFieldReplaceableUnitIds5g) {
//						
//					sb.append("          <RiLink xmlns=\"urn:com:ericsson:ecim:ReqRiLink\">" + eol);
//					sb.append("            <riLinkId>BB-01-A-" + strCurrFruId + "-Data1</riLinkId>" + eol);
//					sb.append("            <riPortRef1>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01,RiPort=A</riPortRef1>" + eol);
//					sb.append("            <riPortRef2>ManagedElement=1,Equipment=1,FieldReplaceableUnit=" + strCurrFruId + ",RiPort=DATA_1</riPortRef2>" + eol);
//					sb.append("          </RiLink>" + eol);
//					sb.append("          <RiLink xmlns=\"urn:com:ericsson:ecim:ReqRiLink\">" + eol);
//					sb.append("            <riLinkId>BB-01-B-" + strCurrFruId + "-Data2</riLinkId>" + eol);
//					sb.append("            <riPortRef1>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01,RiPort=B</riPortRef1>" + eol);
//					sb.append("            <riPortRef2>ManagedElement=1,Equipment=1,FieldReplaceableUnit=" + strCurrFruId + ",RiPort=DATA_2</riPortRef2>" + eol);
//					sb.append("          </RiLink>" + eol);
//				}
//			}
			sb.append("        </Equipment>" + eol); 
			sb.append("        <EquipmentSupportFunction xmlns=\"urn:com:ericsson:ecim:ResEquipmentSupportFunction\">" + eol);
			sb.append("          <equipmentSupportFunctionId>1</equipmentSupportFunctionId>" + eol);
			sb.append("          <supportSystemControl>" + supportSystemControl + "</supportSystemControl>" + eol);
			sb.append("          <Climate xmlns=\"urn:com:ericsson:ecim:ResClimate\">" + eol);
			sb.append("            <climateId>1</climateId>" + eol);
			sb.append("            <controlDomainRef>ManagedElement=1,Equipment=1,Cabinet=1</controlDomainRef>" + eol);
			sb.append("            <climateControlMode>NORMAL</climateControlMode>" + eol);
			sb.append("          </Climate>" + eol);
			sb.append("        </EquipmentSupportFunction>" + eol);
			sb.append("        <NodeSupport xmlns=\"urn:com:ericsson:ecim:RmeSupport\">" + eol);
			sb.append("          <nodeSupportId>1</nodeSupportId>" + eol);
			sb.append("          <MpClusterHandling xmlns=\"urn:com:ericsson:ecim:RmeMpClusterHandling\">" + eol);
			sb.append("            <mpClusterHandlingId>1</mpClusterHandlingId>" + eol);
			sb.append("            <primaryCoreRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=" + fieldReplaceableUnitId + "</primaryCoreRef>" + eol);
			sb.append("          </MpClusterHandling>" + eol);

//			if(duInfo.isMmWave)//TMO_202 - removing to keep a standard 
//			{
//				for(String strCurrFruId : duInfo.rndFieldReplaceableUnitIds5g) {
//						sb.append("          <SectorEquipmentFunction xmlns=\"urn:com:ericsson:ecim:RmeSectorEquipmentFunction\">" + eol);
//						sb.append("            <sectorEquipmentFunctionId>" + strCurrFruId + "</sectorEquipmentFunctionId>" + eol);
//						sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
//						sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=" + strCurrFruId + ",Transceiver=1</rfBranchRef>" + eol);
//						sb.append("          </SectorEquipmentFunction>" + eol);
//
//				}
//			}
			sb.append("        </NodeSupport>" + eol);
			sb.append("      </ManagedElement>" + eol);
			sb.append("    </config>" + eol);
			sb.append("  </edit-config>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"Closing\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <close-session></close-session>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);

			FileUtil.writeToFile(sb, file);

		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNRSiteEquipmentNetConf exception!", ex);
			Logger.getGmoLogger().printError("Error generating SiteEquipment script! " + ex.getMessage());
		}
	}

	// Deprecated
	private void generate5GNR600SiteEquipmentNetConfMTR1923(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<hello xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <capabilities>" + eol);
			sb.append("    <capability>urn:ietf:params:netconf:base:1.0</capability>" + eol);
			sb.append("  </capabilities>" + eol);
			sb.append("</hello>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"1\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <edit-config>" + eol);
			sb.append("    <target>" + eol);
			sb.append("      <running />" + eol);
			sb.append("    </target>" + eol);
			sb.append("    <config xmlns:xc=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("      <ManagedElement xmlns=\"urn:com:ericsson:ecim:ComTop\">" + eol);
			sb.append("        <managedElementId>1</managedElementId>" + eol);
			sb.append("        <userLabel>" + duInfo.duName + "</userLabel>" + eol);
			sb.append("        <Equipment xmlns=\"urn:com:ericsson:ecim:ReqEquipment\">" + eol);
			sb.append("          <equipmentId>1</equipmentId>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>1</antennaUnitGroupId>" + eol);
			sb.append("            <AntennaUnit>" + eol);
			sb.append("              <antennaUnitId>1</antennaUnitId>" + eol);
			sb.append("              <AntennaSubunit>" + eol);
			sb.append("                <antennaSubunitId>1</antennaSubunitId>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>0</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>1</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>2</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>3</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("              </AntennaSubunit>" + eol);
			sb.append("            </AntennaUnit>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-01</fieldReplaceableUnitId>" + eol);
			sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>A</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>1</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>1</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=1,AntennaUnit=1,AntennaSubunit=1,AuPort=0</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-01,RfPort=A</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-01</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>C</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>1</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>2</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=1,AntennaUnit=1,AntennaSubunit=1,AuPort=2</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-01,RfPort=C</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-01</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>B</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>1</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>3</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=1,AntennaUnit=1,AntennaSubunit=1,AuPort=1</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-01,RfPort=B</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-01</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>D</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>1</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>4</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=1,AntennaUnit=1,AntennaSubunit=1,AuPort=3</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-01,RfPort=D</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>2</antennaUnitGroupId>" + eol);
			sb.append("            <AntennaUnit>" + eol);
			sb.append("              <antennaUnitId>1</antennaUnitId>" + eol);
			sb.append("              <AntennaSubunit>" + eol);
			sb.append("                <antennaSubunitId>1</antennaSubunitId>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>0</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>1</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>2</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>3</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("              </AntennaSubunit>" + eol);
			sb.append("            </AntennaUnit>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-02</fieldReplaceableUnitId>" + eol);
			sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>A</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>2</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>1</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=2,AntennaUnit=1,AntennaSubunit=1,AuPort=0</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-02,RfPort=A</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-02</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>C</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>2</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>2</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=2,AntennaUnit=1,AntennaSubunit=1,AuPort=2</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-02,RfPort=C</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-02</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>B</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>2</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>3</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=2,AntennaUnit=1,AntennaSubunit=1,AuPort=1</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-02,RfPort=B</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-02</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>D</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>2</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>4</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=2,AntennaUnit=1,AntennaSubunit=1,AuPort=3</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-02,RfPort=D</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>3</antennaUnitGroupId>" + eol);
			sb.append("            <AntennaUnit>" + eol);
			sb.append("              <antennaUnitId>1</antennaUnitId>" + eol);
			sb.append("              <AntennaSubunit>" + eol);
			sb.append("                <antennaSubunitId>1</antennaSubunitId>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>0</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>1</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>2</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("                <AuPort>" + eol);
			sb.append("                  <auPortId>3</auPortId>" + eol);
			sb.append("                </AuPort>" + eol);
			sb.append("              </AntennaSubunit>" + eol);
			sb.append("            </AntennaUnit>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-03</fieldReplaceableUnitId>" + eol);
			sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>A</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>3</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>1</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=3,AntennaUnit=1,AntennaSubunit=1,AuPort=0</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-03,RfPort=A</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-03</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>C</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>3</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>2</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=3,AntennaUnit=1,AntennaSubunit=1,AuPort=2</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-03,RfPort=C</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-03</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>B</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>3</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>3</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=3,AntennaUnit=1,AntennaSubunit=1,AuPort=1</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-03,RfPort=B</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-03</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>D</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <AntennaUnitGroup xmlns=\"urn:com:ericsson:ecim:ReqAntennaSystem\">" + eol);
			sb.append("            <antennaUnitGroupId>3</antennaUnitGroupId>" + eol);
			sb.append("            <RfBranch>" + eol);
			sb.append("              <rfBranchId>4</rfBranchId>" + eol);
			sb.append("              <auPortRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=3,AntennaUnit=1,AntennaSubunit=1,AuPort=3</auPortRef>" + eol);
			sb.append("              <rfPortRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-03,RfPort=D</rfPortRef>" + eol);
			sb.append("            </RfBranch>" + eol);
			sb.append("          </AntennaUnitGroup>" + eol);
			sb.append("          <Cabinet xmlns=\"urn:com:ericsson:ecim:ReqCabinet\">" + eol);
			sb.append("            <cabinetId>1</cabinetId>" + eol);
			sb.append("            <climateSystem>STANDARD</climateSystem>" + eol);
			sb.append("          </Cabinet>" + eol);
			sb.append("          <EcBus xmlns=\"urn:com:ericsson:ecim:ReqEcBus\">" + eol);
			sb.append("            <ecBusId>1</ecBusId>" + eol);
			sb.append("            <ecBusConnectorRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01</ecBusConnectorRef>" + eol);
			sb.append("          </EcBus>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>BB-01</fieldReplaceableUnitId>" + eol);
			sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            <EcPort xmlns=\"urn:com:ericsson:ecim:ReqEcPort\">" + eol);
			sb.append("              <ecPortId>1</ecPortId>" + eol);
			sb.append("              <hubPosition>A6</hubPosition>" + eol);
			sb.append("              <ecBusRef>ManagedElement=1,Equipment=1,EcBus=1</ecBusRef>" + eol);
			sb.append("            </EcPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>A</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>B</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>C</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>D</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>E</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>F</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>G</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>H</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>J</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>K</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>L</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>M</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>N</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>P</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>Q</riPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-01</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>R</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>DATA_1</riPortId>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>DATA_2</riPortId>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-02</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>R</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>DATA_1</riPortId>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>DATA_2</riPortId>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>6-03</fieldReplaceableUnitId>" + eol);
			sb.append("            <RfPort xmlns=\"urn:com:ericsson:ecim:ReqRfPort\">" + eol);
			sb.append("              <rfPortId>R</rfPortId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            </RfPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>DATA_1</riPortId>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("            <RiPort xmlns=\"urn:com:ericsson:ecim:ReqRiPort\">" + eol);
			sb.append("              <riPortId>DATA_2</riPortId>" + eol);
			sb.append("            </RiPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("          <RiLink xmlns=\"urn:com:ericsson:ecim:ReqRiLink\">" + eol);
			sb.append("            <riLinkId>BB-01-A-6-01-Data2</riLinkId>" + eol);
			sb.append("            <riPortRef1>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01,RiPort=A</riPortRef1>" + eol);
			sb.append("            <riPortRef2>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-01,RiPort=DATA_2</riPortRef2>" + eol);
			sb.append("          </RiLink>" + eol);
			sb.append("          <RiLink xmlns=\"urn:com:ericsson:ecim:ReqRiLink\">" + eol);
			sb.append("            <riLinkId>BB-01-B-6-02-Data2</riLinkId>" + eol);
			sb.append("            <riPortRef1>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01,RiPort=B</riPortRef1>" + eol);
			sb.append("            <riPortRef2>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-02,RiPort=DATA_2</riPortRef2>" + eol);
			sb.append("          </RiLink>" + eol);
			sb.append("          <RiLink xmlns=\"urn:com:ericsson:ecim:ReqRiLink\">" + eol);
			sb.append("            <riLinkId>BB-01-C-6-03-Data2</riLinkId>" + eol);
			sb.append("            <riPortRef1>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01,RiPort=C</riPortRef1>" + eol);
			sb.append("            <riPortRef2>ManagedElement=1,Equipment=1,FieldReplaceableUnit=6-03,RiPort=DATA_2</riPortRef2>" + eol);
			sb.append("          </RiLink>" + eol);
			sb.append("        </Equipment>" + eol);
			sb.append("        <EquipmentSupportFunction xmlns=\"urn:com:ericsson:ecim:ResEquipmentSupportFunction\">" + eol);
			sb.append("          <equipmentSupportFunctionId>1</equipmentSupportFunctionId>" + eol);
			sb.append("          <supportSystemControl>true</supportSystemControl>" + eol);
			sb.append("          <Climate xmlns=\"urn:com:ericsson:ecim:ResClimate\">" + eol);
			sb.append("            <climateId>1</climateId>" + eol);
			sb.append("            <controlDomainRef>ManagedElement=1,Equipment=1,Cabinet=1</controlDomainRef>" + eol);
			sb.append("            <climateControlMode>NORMAL</climateControlMode>" + eol);
			sb.append("          </Climate>" + eol);
			sb.append("        </EquipmentSupportFunction>" + eol);
			sb.append("        <NodeSupport xmlns=\"urn:com:ericsson:ecim:RmeSupport\">" + eol);
			sb.append("          <nodeSupportId>1</nodeSupportId>" + eol);
			sb.append("          <MpClusterHandling xmlns=\"urn:com:ericsson:ecim:RmeMpClusterHandling\">" + eol);
			sb.append("            <mpClusterHandlingId>1</mpClusterHandlingId>" + eol);
			sb.append("            <primaryCoreRef>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01</primaryCoreRef>" + eol);
			sb.append("          </MpClusterHandling>" + eol);
			sb.append("          <SectorEquipmentFunction xmlns=\"urn:com:ericsson:ecim:RmeSectorEquipmentFunction\">" + eol);
			sb.append("            <sectorEquipmentFunctionId>6-01</sectorEquipmentFunctionId>" + eol);
			sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=1,RfBranch=1</rfBranchRef>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=1,RfBranch=2</rfBranchRef>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=1,RfBranch=3</rfBranchRef>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=1,RfBranch=4</rfBranchRef>" + eol);
			sb.append("          </SectorEquipmentFunction>" + eol);
			sb.append("          <SectorEquipmentFunction xmlns=\"urn:com:ericsson:ecim:RmeSectorEquipmentFunction\">" + eol);
			sb.append("            <sectorEquipmentFunctionId>6-02</sectorEquipmentFunctionId>" + eol);
			sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=2,RfBranch=1</rfBranchRef>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=2,RfBranch=2</rfBranchRef>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=2,RfBranch=3</rfBranchRef>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=2,RfBranch=4</rfBranchRef>" + eol);
			sb.append("          </SectorEquipmentFunction>" + eol);
			sb.append("          <SectorEquipmentFunction xmlns=\"urn:com:ericsson:ecim:RmeSectorEquipmentFunction\">" + eol);
			sb.append("            <sectorEquipmentFunctionId>6-03</sectorEquipmentFunctionId>" + eol);
			sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=3,RfBranch=1</rfBranchRef>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=3,RfBranch=2</rfBranchRef>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=3,RfBranch=3</rfBranchRef>" + eol);
			sb.append("            <rfBranchRef>ManagedElement=1,Equipment=1,AntennaUnitGroup=3,RfBranch=4</rfBranchRef>" + eol);
			sb.append("          </SectorEquipmentFunction>" + eol);
			sb.append("        </NodeSupport>" + eol);
			sb.append("      </ManagedElement>" + eol);
			sb.append("    </config>" + eol);
			sb.append("  </edit-config>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"Closing\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <close-session></close-session>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);

			FileUtil.writeToFile(sb, file);

		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNR600SiteEquipmentNetConfMTR1923 exception!", ex);
			Logger.getGmoLogger().printError("Error generating SiteEquipment script! " + ex.getMessage());
		}
	}

	// Deprecated
	/*private void generate5GNRSiteBasicNetConf(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<hello xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <capabilities>" + eol);
			sb.append("    <capability>urn:ietf:params:netconf:base:1.0</capability>" + eol);
			sb.append("  </capabilities>" + eol);
			sb.append("</hello>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"1\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <edit-config>" + eol);
			sb.append("    <target>" + eol);
			sb.append("      <running />" + eol);
			sb.append("    </target>" + eol);
			sb.append("    <config xmlns:xc=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("      <ManagedElement xmlns=\"urn:com:ericsson:ecim:ComTop\">" + eol);
			sb.append("        <managedElementId>1</managedElementId>" + eol);
			sb.append("        <dnPrefix>SubNetwork=ONRM_ROOT_MO,SubNetwork=" + duInfo.subNetwork + ",MeContext=" + duInfo.duName + "</dnPrefix>" + eol);
			sb.append("        <SystemFunctions>" + eol);
			sb.append("          <systemFunctionsId>1</systemFunctionsId>" + eol);
			sb.append("          <Lm xmlns=\"urn:com:ericsson:ecim:RcsLM\">" + eol);
			sb.append("            <lmId>1</lmId>" + eol);
			sb.append("            <fingerprint>" + duInfo.duName + "</fingerprint>" + eol);
			sb.append("          </Lm>" + eol);
			sb.append("        </SystemFunctions>" + eol);
			sb.append("      </ManagedElement>" + eol);
			sb.append("    </config>" + eol);
			sb.append("  </edit-config>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"Closing\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <close-session></close-session>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<hello xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <capabilities>" + eol);
			sb.append("    <capability>urn:ietf:params:netconf:base:1.0</capability>" + eol);
			sb.append("  </capabilities>" + eol);
			sb.append("</hello>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"2\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <edit-config>" + eol);
			sb.append("    <target>" + eol);
			sb.append("      <running />" + eol);
			sb.append("    </target>" + eol);
			sb.append("    <config xmlns:xc=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("      <ManagedElement xmlns=\"urn:com:ericsson:ecim:ComTop\">" + eol);
			sb.append("        <managedElementId>1</managedElementId>" + eol);
			sb.append("        <SystemFunctions>" + eol);
			sb.append("          <systemFunctionsId>1</systemFunctionsId>" + eol);
			sb.append("          <Lm xmlns=\"urn:com:ericsson:ecim:RcsLM\">" + eol);
			sb.append("            <lmId>1</lmId>" + eol);
			sb.append("            <FeatureState>" + eol);
			sb.append("              <featureStateId>CXC4011823</featureStateId>" + eol);
			sb.append("              <featureState>ACTIVATED</featureState>" + eol);
			sb.append("            </FeatureState>" + eol);
			sb.append("            <FeatureState>" + eol);
			sb.append("              <featureStateId>CXC4012051</featureStateId>" + eol);
			sb.append("              <featureState>ACTIVATED</featureState>" + eol);
			sb.append("            </FeatureState>" + eol);
			sb.append("            <FeatureState>" + eol);
			sb.append("              <featureStateId>CXC4011838</featureStateId>" + eol);
			sb.append("              <featureState>ACTIVATED</featureState>" + eol);
			sb.append("            </FeatureState>" + eol);
			sb.append("          </Lm>" + eol);
			sb.append("        </SystemFunctions>" + eol);
			sb.append("      </ManagedElement>" + eol);
			sb.append("    </config>" + eol);
			sb.append("  </edit-config>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"Closing\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <close-session></close-session>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<hello xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <capabilities>" + eol);
			sb.append("    <capability>urn:ietf:params:netconf:base:1.0</capability>" + eol);
			sb.append("  </capabilities>" + eol);
			sb.append("</hello>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"3\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <edit-config>" + eol);
			sb.append("    <target>" + eol);
			sb.append("      <running />" + eol);
			sb.append("    </target>" + eol);
			sb.append("    <config xmlns:xc=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("      <ManagedElement xmlns=\"urn:com:ericsson:ecim:ComTop\">" + eol);
			sb.append("        <managedElementId>1</managedElementId>" + eol);
			sb.append("        <SystemFunctions>" + eol);
			sb.append("          <systemFunctionsId>1</systemFunctionsId>" + eol);
			sb.append("          <SecM xmlns=\"urn:com:ericsson:ecim:RcsSecM\">" + eol);
			sb.append("            <secMId>1</secMId>" + eol);
			sb.append("            <UserManagement>" + eol);
			sb.append("              <userManagementId>1</userManagementId>" + eol);
			sb.append("              <UserIdentity xmlns=\"urn:com:ericsson:ecim:RcsUser\">" + eol);
			sb.append("                <userIdentityId>1</userIdentityId>" + eol);
			sb.append("                <MaintenanceUser>" + eol);
			sb.append("                  <maintenanceUserId>1</maintenanceUserId>" + eol);
			sb.append("                  <userName>prbs</userName>" + eol);
			sb.append("                  <password>" + eol);
			sb.append("                    <cleartext />" + eol);
			sb.append("                    <password>prbs1234</password>" + eol);
			sb.append("                  </password>" + eol);
			sb.append("                </MaintenanceUser>" + eol);
			sb.append("              </UserIdentity>" + eol);
			sb.append("            </UserManagement>" + eol);
			sb.append("          </SecM>" + eol);
			sb.append("          <SysM xmlns=\"urn:com:ericsson:ecim:RcsSysM\">" + eol);
			sb.append("            <sysMId>1</sysMId>" + eol);
			sb.append("            <CliTls>" + eol);		// [05292020] TC_299
			sb.append("              <cliTlsId>1</cliTlsId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("              <trustCategory>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,TrustCategory=oamTrustCategory</trustCategory>" + eol);
			sb.append("              <nodeCredential>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,NodeCredential=oamNodeCredential</nodeCredential>" + eol);
			sb.append("            </CliTls>" + eol);
			sb.append("            <HttpM xmlns=\"urn:com:ericsson:ecim:RcsHttpM\">" + eol);
			sb.append("              <httpMId>1</httpMId>" + eol);
			sb.append("              <Https>" + eol);
			sb.append("                <httpsId>1</httpsId>" + eol);
			sb.append("                <nodeCredential>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,NodeCredential=oamNodeCredential</nodeCredential>" + eol);
			sb.append("                <trustCategory>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,TrustCategory=oamTrustCategory</trustCategory>" + eol);
			sb.append("              </Https>" + eol);
			sb.append("            </HttpM>" + eol);
			sb.append("          </SysM>" + eol);
			sb.append("        </SystemFunctions>" + eol);
			sb.append("        <Transport>" + eol);
			sb.append("          <transportId>1</transportId>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_OAM</routerId>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("        </Transport>" + eol);
			sb.append("        <Equipment xmlns=\"urn:com:ericsson:ecim:ReqEquipment\">" + eol);
			sb.append("          <equipmentId>1</equipmentId>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>BB-01</fieldReplaceableUnitId>" + eol);
			sb.append("            <TnPort xmlns=\"urn:com:ericsson:ecim:ReqTnPort\">" + eol);
			sb.append("              <tnPortId>TN_A</tnPortId>" + eol);
			sb.append("            </TnPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("        </Equipment>" + eol);
			sb.append("        <Transport>" + eol);
			sb.append("          <transportId>1</transportId>" + eol);
			sb.append("          <EthernetPort xmlns=\"urn:com:ericsson:ecim:RtnL2EthernetPort\">" + eol);
			sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            <admOperatingMode>" + duInfo.ethernetPortObj.getAdmOperatingMode() + "</admOperatingMode>" + eol);
			sb.append("            <autoNegEnable>" + duInfo.ethernetPortObj.getAutoNegEnable() + "</autoNegEnable>" + eol);
			sb.append("            <encapsulation>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01,TnPort=TN_A</encapsulation>" + eol);
			sb.append("            <ethernetPortId>TN_A</ethernetPortId>" + eol);
			sb.append("          </EthernetPort>" + eol);
			sb.append("          <VlanPort xmlns=\"urn:com:ericsson:ecim:RtnL2VlanPort\">" + eol);
			sb.append("            <encapsulation>ManagedElement=1,Transport=1,EthernetPort=TN_A</encapsulation>" + eol);
			sb.append("            <vlanId>" + duInfo.oamVlanId + "</vlanId>" + eol);
			sb.append("            <vlanPortId>" + duInfo.oamVlanId + "</vlanPortId>" + eol);
			sb.append("          </VlanPort>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_OAM</routerId>" + eol);
			sb.append("            <InterfaceIPv4 xmlns=\"urn:com:ericsson:ecim:RtnL3InterfaceIPv4\">" + eol);
			sb.append("              <encapsulation>ManagedElement=1,Transport=1,VlanPort=" + duInfo.oamVlanId + "</encapsulation>" + eol);
			sb.append("              <interfaceIPv4Id>1</interfaceIPv4Id>" + eol);
			sb.append("              <routesHoldDownTimer>180</routesHoldDownTimer>" + eol);
			sb.append("              <AddressIPv4>" + eol);
			sb.append("                <address>" + duInfo.oamIP + "/27</address>" + eol);
			sb.append("                <addressIPv4Id>1</addressIPv4Id>" + eol);
			sb.append("              </AddressIPv4>" + eol);
			sb.append("            </InterfaceIPv4>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("        </Transport>" + eol);
			sb.append("        <SystemFunctions>" + eol);
			sb.append("          <systemFunctionsId>1</systemFunctionsId>" + eol);
			sb.append("          <SysM xmlns=\"urn:com:ericsson:ecim:RcsSysM\">" + eol);
			sb.append("            <sysMId>1</sysMId>" + eol);
			sb.append("            <OamAccessPoint>" + eol);
			sb.append("              <oamAccessPointId>1</oamAccessPointId>" + eol);
			sb.append("              <accessPoint>ManagedElement=1,Transport=1,Router=vr_OAM,InterfaceIPv4=1,AddressIPv4=1</accessPoint>" + eol);
			sb.append("            </OamAccessPoint>" + eol);
			sb.append("            <OamTrafficClass>" + eol);
			sb.append("              <oamTrafficClassId>1</oamTrafficClassId>" + eol);
			sb.append("              <dscp>8</dscp>" + eol);
			sb.append("            </OamTrafficClass>" + eol);
			sb.append("            <TimeM xmlns=\"urn:com:ericsson:ecim:RcsTimeM\">" + eol);
			sb.append("              <timeMId>1</timeMId>" + eol);
			sb.append("              <DateAndTime>" + eol);
			sb.append("                <dateAndTimeId>1</dateAndTimeId>" + eol);
			sb.append("                <timeZone>" + duInfo.pciSiteObj.timeZoneARNE + "</timeZone>" + eol);
			sb.append("              </DateAndTime>" + eol);
			sb.append("              <Ntp>" + eol);
			sb.append("                <ntpId>1</ntpId>" + eol);
			sb.append("                <NtpServer>" + eol);
			sb.append("                  <userLabel>NTP1</userLabel>" + eol);
			sb.append("                  <ntpServerId>1</ntpServerId>" + eol);
			sb.append("                  <serverAddress>" + duInfo.ipInfo.ntpPrimaryIP + "</serverAddress>" + eol);
			sb.append("                  <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("                </NtpServer>" + eol);
			sb.append("                <NtpServer>" + eol);
			sb.append("                  <userLabel>NTP2</userLabel>" + eol);
			sb.append("                  <ntpServerId>2</ntpServerId>" + eol);
			sb.append("                  <serverAddress>" + duInfo.ipInfo.ntpSecondaryIP + "</serverAddress>" + eol);
			sb.append("                  <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("                </NtpServer>" + eol);
			sb.append("              </Ntp>" + eol);
			sb.append("            </TimeM>" + eol);
			sb.append("          </SysM>" + eol);
			sb.append("        </SystemFunctions>" + eol);
			sb.append("        <Transport>" + eol);
			sb.append("          <transportId>1</transportId>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_TRAFFIC</routerId>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("          <VlanPort xmlns=\"urn:com:ericsson:ecim:RtnL2VlanPort\">" + eol);
			sb.append("            <encapsulation>ManagedElement=1,Transport=1,EthernetPort=TN_A</encapsulation>" + eol);
			sb.append("            <vlanId>" + duInfo.s1VlanId + "</vlanId>" + eol);
			sb.append("            <vlanPortId>" + duInfo.s1VlanId + "</vlanPortId>" + eol);
			sb.append("          </VlanPort>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_TRAFFIC</routerId>" + eol);
			sb.append("            <InterfaceIPv4 xmlns=\"urn:com:ericsson:ecim:RtnL3InterfaceIPv4\">" + eol);
			sb.append("              <encapsulation>ManagedElement=1,Transport=1,VlanPort=" + duInfo.s1VlanId + "</encapsulation>" + eol);
			sb.append("              <interfaceIPv4Id>1</interfaceIPv4Id>" + eol);
			sb.append("              <routesHoldDownTimer>180</routesHoldDownTimer>" + eol);
			sb.append("              <AddressIPv4>" + eol);
			sb.append("                <address>" + duInfo.s1ControlPlaneIp + "/29</address>" + eol);
			sb.append("                <addressIPv4Id>1</addressIPv4Id>" + eol);
			sb.append("              </AddressIPv4>" + eol);
			sb.append("            </InterfaceIPv4>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_OAM</routerId>" + eol);
			sb.append("            <RouteTableIPv4Static xmlns=\"urn:com:ericsson:ecim:RtnRoutesStaticRouteIPv4\">" + eol);
			sb.append("              <routeTableIPv4StaticId>1</routeTableIPv4StaticId>" + eol);
			sb.append("              <Dst>" + eol);
			sb.append("                <dst>0.0.0.0/0</dst>" + eol);
			sb.append("                <dstId>1</dstId>" + eol);
			sb.append("                <NextHop>" + eol);
			sb.append("                  <address>" + duInfo.oamDefaultRouter + "</address>" + eol);
			sb.append("                  <adminDistance>10</adminDistance>" + eol);
			sb.append("                  <nextHopId>1</nextHopId>" + eol);
			sb.append("                </NextHop>" + eol);
			sb.append("              </Dst>" + eol);
			sb.append("            </RouteTableIPv4Static>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_TRAFFIC</routerId>" + eol);
			sb.append("            <RouteTableIPv4Static xmlns=\"urn:com:ericsson:ecim:RtnRoutesStaticRouteIPv4\">" + eol);
			sb.append("              <routeTableIPv4StaticId>1</routeTableIPv4StaticId>" + eol);
			sb.append("              <Dst>" + eol);
			sb.append("                <dst>0.0.0.0/0</dst>" + eol);
			sb.append("                <dstId>1</dstId>" + eol);
			sb.append("                <NextHop>" + eol);
			sb.append("                  <address>" + duInfo.corenetDefaultGateway + "</address>" + eol);
			sb.append("                  <adminDistance>10</adminDistance>" + eol);
			sb.append("                  <nextHopId>1</nextHopId>" + eol);
			sb.append("                </NextHop>" + eol);
			sb.append("              </Dst>" + eol);
			sb.append("            </RouteTableIPv4Static>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("          <Synchronization xmlns=\"urn:com:ericsson:ecim:RsyncSynchronization\">" + eol);
			sb.append("            <synchronizationId>1</synchronizationId>" + eol);
			sb.append("            <RadioEquipmentClock xmlns=\"urn:com:ericsson:ecim:RsyncRadioEquipmentClock\">" + eol);
			sb.append("              <radioEquipmentClockId>1</radioEquipmentClockId>" + eol);
			sb.append("            </RadioEquipmentClock>" + eol);
			sb.append("          </Synchronization>" + eol);
			sb.append("        </Transport>" + eol);
			sb.append("        <Equipment xmlns=\"urn:com:ericsson:ecim:ReqEquipment\">" + eol);
			sb.append("          <equipmentId>1</equipmentId>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>BB-01</fieldReplaceableUnitId>" + eol);
			sb.append("            <SyncPort xmlns=\"urn:com:ericsson:ecim:ReqSyncPort\">" + eol);
			sb.append("              <syncPortId>1</syncPortId>" + eol);
			sb.append("            </SyncPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("        </Equipment>" + eol);
			sb.append("        <Transport>" + eol);
			sb.append("          <transportId>1</transportId>" + eol);
			sb.append("          <Synchronization xmlns=\"urn:com:ericsson:ecim:RsyncSynchronization\">" + eol);
			sb.append("            <synchronizationId>1</synchronizationId>" + eol);
			sb.append("            <TimeSyncIO xmlns=\"urn:com:ericsson:ecim:RsyncTimeSyncIO\">" + eol);
			sb.append("              <compensationDelay>0</compensationDelay>" + eol);
			sb.append("              <encapsulation>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01,SyncPort=1</encapsulation>" + eol);
			sb.append("              <timeSyncIOId>1</timeSyncIOId>" + eol);
			sb.append("            </TimeSyncIO>" + eol);
			sb.append("            <RadioEquipmentClock xmlns=\"urn:com:ericsson:ecim:RsyncRadioEquipmentClock\">" + eol);
			sb.append("              <radioEquipmentClockId>1</radioEquipmentClockId>" + eol);
			sb.append("              <RadioEquipmentClockReference>" + eol);
			sb.append("                <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("                <encapsulation>ManagedElement=1,Transport=1,Synchronization=1,TimeSyncIO=1</encapsulation>" + eol);
			sb.append("                <priority>1</priority>" + eol);
			sb.append("                <radioEquipmentClockReferenceId>1</radioEquipmentClockReferenceId>" + eol);
			sb.append("                <useQLFrom>ADMIN_QL</useQLFrom>" + eol);
			sb.append("                <adminQualityLevel>" + eol);
			sb.append("                  <qualityLevelValueOptionI>SSU_A</qualityLevelValueOptionI>" + eol);
			sb.append("                  <qualityLevelValueOptionII>STU</qualityLevelValueOptionII>" + eol);
			sb.append("                  <qualityLevelValueOptionIII>UNK</qualityLevelValueOptionIII>" + eol);
			sb.append("                </adminQualityLevel>" + eol);
			sb.append("              </RadioEquipmentClockReference>" + eol);
			sb.append("            </RadioEquipmentClock>" + eol);
			sb.append("            <TimeSyncIO xmlns=\"urn:com:ericsson:ecim:RsyncTimeSyncIO\">" + eol);
			sb.append("              <timeSyncIOId>1</timeSyncIOId>" + eol);
			sb.append("              <GnssInfo xmlns=\"urn:com:ericsson:ecim:RsyncGnssInfo\">" + eol);
			sb.append("                <gnssInfoId>1</gnssInfoId>" + eol);
			sb.append("              </GnssInfo>" + eol);
			sb.append("            </TimeSyncIO>" + eol);
			sb.append("          </Synchronization>" + eol);
			sb.append("        </Transport>" + eol);
			sb.append("        <NodeSupport xmlns=\"urn:com:ericsson:ecim:RmeSupport\">" + eol);
			sb.append("          <nodeSupportId>1</nodeSupportId>" + eol);
			sb.append("          <ServiceDiscovery xmlns=\"urn:com:ericsson:ecim:RmeSds\">" + eol);
			sb.append("            <serviceDiscoveryId>1</serviceDiscoveryId>" + eol);
			sb.append("            <localAddress>ManagedElement=1,Transport=1,Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1</localAddress>" + eol);
			sb.append("            <trustCategory>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,TrustCategory=oamTrustCategory</trustCategory>" + eol);
			sb.append("            <nodeCredential>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,NodeCredential=oamNodeCredential</nodeCredential>" + eol);
			sb.append("            <primaryGsds>" + eol);
			sb.append("              <host>localhost</host>" + eol);
			sb.append("              <port>8301</port>" + eol);
			sb.append("              <serviceArea>NR</serviceArea>" + eol);
			sb.append("            </primaryGsds>" + eol);
			sb.append("          </ServiceDiscovery>" + eol);
			sb.append("          <ServiceDiscoveryServer xmlns=\"urn:com:ericsson:ecim:RmeSdsServer\">" + eol);
			sb.append("            <serviceDiscoveryServerId>1</serviceDiscoveryServerId>" + eol);
			sb.append("            <localAddress>ManagedElement=1,Transport=1,Router=vr_TRAFFIC,InterfaceIPv4=1,AddressIPv4=1</localAddress>" + eol);
			sb.append("            <trustCategory>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,TrustCategory=oamTrustCategory</trustCategory>" + eol);
			sb.append("            <nodeCredential>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,NodeCredential=oamNodeCredential</nodeCredential>" + eol);
			sb.append("            <cluster>" + eol);
			sb.append("              <host>localhost</host>" + eol);
			sb.append("              <port>8301</port>" + eol);
			sb.append("              <serviceArea>NR</serviceArea>" + eol);
			sb.append("            </cluster>" + eol);
			sb.append("          </ServiceDiscoveryServer>" + eol);
			sb.append("        </NodeSupport>" + eol);
			sb.append("      </ManagedElement>" + eol);
			sb.append("    </config>" + eol);
			sb.append("  </edit-config>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"Closing\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <close-session></close-session>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<hello xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <capabilities>" + eol);
			sb.append("    <capability>urn:ietf:params:netconf:base:1.0</capability>" + eol);
			sb.append("  </capabilities>" + eol);
			sb.append("</hello>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"4\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <edit-config>" + eol);
			sb.append("    <target>" + eol);
			sb.append("      <running />" + eol);
			sb.append("    </target>" + eol);
			sb.append("    <config xmlns:xc=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("      <ManagedElement xmlns=\"urn:com:ericsson:ecim:ComTop\">" + eol);
			sb.append("        <managedElementId>1</managedElementId>" + eol);
			sb.append("        <networkManagedElementId>" + duInfo.duName + "</networkManagedElementId>" + eol);
			sb.append("      </ManagedElement>" + eol);
			sb.append("    </config>" + eol);
			sb.append("  </edit-config>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"Closing\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <close-session></close-session>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);

			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNRSiteBasicNetConf exception!", ex);
			Logger.getGmoLogger().printError("Error generating SiteBasic script! " + ex.getMessage());
		}

	}*/

	private void generate5GNR600SiteBasicNetConf_MTR1923(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();
		//TC-361 30-10-2020
		//[ezrxxsu - 10312020]
		String nodeName = (!duInfo.pciSiteObj.fingerPrint.isEmpty())? duInfo.pciSiteObj.fingerPrint : duInfo.duName;
		try
		{
			String tnPort = "";
			
				if(duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || duInfo.nodeType.contains("6648") || duInfo.nodeType.contains("6651")) {	// [02052021] TC_384 updated for 6648)
					tnPort = "TN_IDL_B";
				}else {
					tnPort = "TN_A";
				}
			
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<hello xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <capabilities>" + eol);
			sb.append("    <capability>urn:ietf:params:netconf:base:1.0</capability>" + eol);
			sb.append("  </capabilities>" + eol);
			sb.append("</hello>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"1\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <edit-config>" + eol);
			sb.append("    <target>" + eol);
			sb.append("      <running />" + eol);
			sb.append("    </target>" + eol);
			sb.append("    <config xmlns:xc=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("      <ManagedElement xmlns=\"urn:com:ericsson:ecim:ComTop\">" + eol);
			sb.append("        <managedElementId>1</managedElementId>" + eol);
			sb.append("        <dnPrefix>SubNetwork=ONRM_ROOT_MO,SubNetwork=" + duInfo.subNetwork + ",MeContext=" + duInfo.duName + "</dnPrefix>" + eol);
			sb.append("        <SystemFunctions>" + eol);
			sb.append("          <systemFunctionsId>1</systemFunctionsId>" + eol);
			sb.append("          <Lm xmlns=\"urn:com:ericsson:ecim:RcsLM\">" + eol);
			sb.append("            <lmId>1</lmId>" + eol);
			if(hasExcaliburSmallCells) {
			sb.append("            <fingerprint>" + duInfo.duName + "</fingerprint>" + eol);
			}else {
				sb.append("            <fingerprint>" + nodeName + "</fingerprint>" + eol);
			}
			sb.append("          </Lm>" + eol);
			sb.append("        </SystemFunctions>" + eol);
			sb.append("      </ManagedElement>" + eol);
			sb.append("    </config>" + eol);
			sb.append("  </edit-config>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"Closing\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <close-session></close-session>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<hello xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <capabilities>" + eol);
			sb.append("    <capability>urn:ietf:params:netconf:base:1.0</capability>" + eol);
			sb.append("  </capabilities>" + eol);
			sb.append("</hello>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"2\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <edit-config>" + eol);
			sb.append("    <target>" + eol);
			sb.append("      <running />" + eol);
			sb.append("    </target>" + eol);
			sb.append("    <config xmlns:xc=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("      <ManagedElement xmlns=\"urn:com:ericsson:ecim:ComTop\">" + eol);
			sb.append("        <managedElementId>1</managedElementId>" + eol);
			sb.append("        <SystemFunctions>" + eol);
			sb.append("          <systemFunctionsId>1</systemFunctionsId>" + eol);
			sb.append("          <Lm xmlns=\"urn:com:ericsson:ecim:RcsLM\">" + eol);
			sb.append("            <lmId>1</lmId>" + eol);
			sb.append("            <FeatureState>" + eol);
			sb.append("              <featureStateId>CXC4011823</featureStateId>" + eol);
			sb.append("              <featureState>ACTIVATED</featureState>" + eol);
			sb.append("            </FeatureState>" + eol);
			// [08042021] Removed feature per feedback from Kartik
//			sb.append("            <FeatureState>" + eol);
//			sb.append("              <featureStateId>CXC4012051</featureStateId>" + eol);
//			sb.append("              <featureState>ACTIVATED</featureState>" + eol);
//			sb.append("            </FeatureState>" + eol);
			
				if(!duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.nodeType.contains("6648") && !duInfo.nodeType.contains("6651")) {	// [02052021] TC_384 updated for 6648
					sb.append("            <FeatureState>" + eol);
					sb.append("              <featureStateId>CXC4011838</featureStateId>" + eol);
					sb.append("              <featureState>ACTIVATED</featureState>" + eol);
					sb.append("            </FeatureState>" + eol);
				}
			
			sb.append("          </Lm>" + eol);
			sb.append("        </SystemFunctions>" + eol);
			sb.append("      </ManagedElement>" + eol);
			sb.append("    </config>" + eol);
			sb.append("  </edit-config>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"Closing\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <close-session></close-session>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<hello xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <capabilities>" + eol);
			sb.append("    <capability>urn:ietf:params:netconf:base:1.0</capability>" + eol);
			sb.append("  </capabilities>" + eol);
			sb.append("</hello>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"3\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <edit-config>" + eol);
			sb.append("    <target>" + eol);
			sb.append("      <running />" + eol);
			sb.append("    </target>" + eol);
			sb.append("    <config xmlns:xc=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("      <ManagedElement xmlns=\"urn:com:ericsson:ecim:ComTop\">" + eol);
			sb.append("        <managedElementId>1</managedElementId>" + eol);
			sb.append("        <SystemFunctions>" + eol);
			sb.append("          <systemFunctionsId>1</systemFunctionsId>" + eol);
			sb.append("          <SecM xmlns=\"urn:com:ericsson:ecim:RcsSecM\">" + eol);
			sb.append("            <secMId>1</secMId>" + eol);
			sb.append("            <UserManagement>" + eol);
			sb.append("              <userManagementId>1</userManagementId>" + eol);
			sb.append("              <UserIdentity xmlns=\"urn:com:ericsson:ecim:RcsUser\">" + eol);
			sb.append("                <userIdentityId>1</userIdentityId>" + eol);
			sb.append("                <MaintenanceUser>" + eol);
			sb.append("                  <maintenanceUserId>1</maintenanceUserId>" + eol);
			sb.append("                  <userName>prbs</userName>" + eol);
			sb.append("                  <password>" + eol);
			sb.append("                    <cleartext />" + eol);
			sb.append("                    <password>prbs1234</password>" + eol);
			sb.append("                  </password>" + eol);
			sb.append("                </MaintenanceUser>" + eol);
			sb.append("              </UserIdentity>" + eol);
			sb.append("            </UserManagement>" + eol);
			sb.append("          </SecM>" + eol);
			sb.append("          <SysM xmlns=\"urn:com:ericsson:ecim:RcsSysM\">" + eol);
			sb.append("            <sysMId>1</sysMId>" + eol);
			sb.append("            <CliTls>" + eol);	// [05292020] TC_299
			sb.append("              <cliTlsId>1</cliTlsId>" + eol);
			sb.append("              <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("              <trustCategory>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,TrustCategory=oamTrustCategory</trustCategory>" + eol);
			sb.append("              <nodeCredential>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,NodeCredential=oamNodeCredential</nodeCredential>" + eol);
			sb.append("            </CliTls>" + eol);
			sb.append("            <HttpM xmlns=\"urn:com:ericsson:ecim:RcsHttpM\">" + eol);
			sb.append("              <httpMId>1</httpMId>" + eol);
			sb.append("              <Https>" + eol);
			sb.append("                <httpsId>1</httpsId>" + eol);
			sb.append("                <nodeCredential>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,NodeCredential=oamNodeCredential</nodeCredential>" + eol);
			sb.append("                <trustCategory>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,TrustCategory=oamTrustCategory</trustCategory>" + eol);
			sb.append("              </Https>" + eol);
			sb.append("            </HttpM>" + eol);
			sb.append("          </SysM>" + eol);
			sb.append("        </SystemFunctions>" + eol);
			sb.append("        <Transport>" + eol);
			sb.append("          <transportId>1</transportId>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_OAM</routerId>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("        </Transport>" + eol);
			sb.append("        <Equipment xmlns=\"urn:com:ericsson:ecim:ReqEquipment\">" + eol);
			sb.append("          <equipmentId>1</equipmentId>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>BB-01</fieldReplaceableUnitId>" + eol);
			sb.append("            <TnPort xmlns=\"urn:com:ericsson:ecim:ReqTnPort\">" + eol);
			sb.append("              <tnPortId>" + tnPort + "</tnPortId>" + eol);
			sb.append("            </TnPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("        </Equipment>" + eol);
			sb.append("        <Transport>" + eol);
			sb.append("          <transportId>1</transportId>" + eol);
			sb.append("          <EthernetPort xmlns=\"urn:com:ericsson:ecim:RtnL2EthernetPort\">" + eol);
			sb.append("            <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("            <admOperatingMode>" + duInfo.ethernetPortObj.getAdmOperatingMode() + "</admOperatingMode>" + eol);
			sb.append("            <autoNegEnable>" + duInfo.ethernetPortObj.getAutoNegEnable() + "</autoNegEnable>" + eol);
			sb.append("            <encapsulation>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01,TnPort=" + tnPort + "</encapsulation>" + eol);
			sb.append("            <ethernetPortId>" + tnPort + "</ethernetPortId>" + eol);
			sb.append("          </EthernetPort>" + eol);
			sb.append("          <VlanPort xmlns=\"urn:com:ericsson:ecim:RtnL2VlanPort\">" + eol);
			sb.append("            <encapsulation>ManagedElement=1,Transport=1,EthernetPort=" + tnPort + "</encapsulation>" + eol);
			if((duInfo.tmoDUInfo.isLowBandMMBBVariation || duInfo.tmoDUInfo.isMidBandTddMMBBVariation || duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode()) && !duInfo.isNRNodeLive && duInfo.is5G) {
				sb.append("            <vlanId>" + duInfo.tmoDUInfo.gNodeBOamVlanId + "</vlanId>" + eol);
				sb.append("            <vlanPortId>" + duInfo.tmoDUInfo.gNodeBOamVlanId + "</vlanPortId>" + eol);
			}else {
				sb.append("            <vlanId>" + duInfo.oamVlanId + "</vlanId>" + eol);
				sb.append("            <vlanPortId>" + duInfo.oamVlanId + "</vlanPortId>" + eol);
			}
			sb.append("          </VlanPort>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_OAM</routerId>" + eol);
			sb.append("            <InterfaceIPv4 xmlns=\"urn:com:ericsson:ecim:RtnL3InterfaceIPv4\">" + eol);
			if((duInfo.tmoDUInfo.isLowBandMMBBVariation || duInfo.tmoDUInfo.isMidBandTddMMBBVariation || duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode()) && !duInfo.isNRNodeLive && duInfo.is5G) {
				sb.append("              <encapsulation>ManagedElement=1,Transport=1,VlanPort=" + duInfo.tmoDUInfo.gNodeBOamVlanId + "</encapsulation>" + eol);
			}else {
				sb.append("              <encapsulation>ManagedElement=1,Transport=1,VlanPort=" + duInfo.oamVlanId + "</encapsulation>" + eol);
			}
			sb.append("              <interfaceIPv4Id>1</interfaceIPv4Id>" + eol);
			sb.append("              <routesHoldDownTimer>180</routesHoldDownTimer>" + eol);
			sb.append("              <AddressIPv4>" + eol);

			String subnetMask = "27";		// hard-coded default
			subnetMask = !duInfo.tmoDUInfo.gNodeBOamNetworkPrefixLength.isEmpty() ? duInfo.tmoDUInfo.gNodeBOamNetworkPrefixLength : subnetMask;	// [12162021] GMO_TMO-214
			if((duInfo.tmoDUInfo.isLowBandMMBBVariation || duInfo.tmoDUInfo.isMidBandTddMMBBVariation || duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode()) && !duInfo.isNRNodeLive && duInfo.is5G) {
				sb.append("                <address>" + duInfo.tmoDUInfo.gNodeBoamIP + "/" + subnetMask + "</address>" + eol);
			}else {
				sb.append("                <address>" + duInfo.oamIP + "/" + subnetMask + "</address>" + eol);
			}
			sb.append("                <addressIPv4Id>1</addressIPv4Id>" + eol);
			sb.append("              </AddressIPv4>" + eol);
			sb.append("            </InterfaceIPv4>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("        </Transport>" + eol);
			sb.append("        <SystemFunctions>" + eol);
			sb.append("          <systemFunctionsId>1</systemFunctionsId>" + eol);
			sb.append("          <SysM xmlns=\"urn:com:ericsson:ecim:RcsSysM\">" + eol);
			sb.append("            <sysMId>1</sysMId>" + eol);
			sb.append("            <OamAccessPoint>" + eol);
			sb.append("              <oamAccessPointId>1</oamAccessPointId>" + eol);
			sb.append("              <accessPoint>ManagedElement=1,Transport=1,Router=vr_OAM,InterfaceIPv4=1,AddressIPv4=1</accessPoint>" + eol);
			sb.append("            </OamAccessPoint>" + eol);
			sb.append("            <OamTrafficClass>" + eol);
			sb.append("              <oamTrafficClassId>1</oamTrafficClassId>" + eol);
			sb.append("              <dscp>8</dscp>" + eol);
			sb.append("            </OamTrafficClass>" + eol);
			sb.append("            <TimeM xmlns=\"urn:com:ericsson:ecim:RcsTimeM\">" + eol);
			sb.append("              <timeMId>1</timeMId>" + eol);
			sb.append("              <DateAndTime>" + eol);
			sb.append("                <dateAndTimeId>1</dateAndTimeId>" + eol);
			sb.append("                <timeZone>" + duInfo.pciSiteObj.timeZoneARNE + "</timeZone>" + eol);
			sb.append("              </DateAndTime>" + eol);
			sb.append("              <Ntp>" + eol);
			sb.append("                <ntpId>1</ntpId>" + eol);
			sb.append("                <NtpServer>" + eol);
			sb.append("                  <userLabel>NTP1</userLabel>" + eol);
			sb.append("                  <ntpServerId>1</ntpServerId>" + eol);
			
			if(isExcaliburToSB ) {
				sb.append("                  <serverAddress>" + duInfo.tmoDUInfo.eNodeBnTPServerPrimaryIPaddress + "</serverAddress>" + eol);
			}else {
				sb.append("                  <serverAddress>" + duInfo.ipInfo.ntpPrimaryIP + "</serverAddress>" + eol);
			}
			sb.append("                  <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("                </NtpServer>" + eol);
			sb.append("                <NtpServer>" + eol);
			sb.append("                  <userLabel>NTP2</userLabel>" + eol);
			sb.append("                  <ntpServerId>2</ntpServerId>" + eol);
			if(isExcaliburToSB ) {
				sb.append("                  <serverAddress>" + duInfo.tmoDUInfo.eNodeBnTPServerSecondaryIPaddress + "</serverAddress>" + eol);
			}else {
				sb.append("                  <serverAddress>" + duInfo.ipInfo.ntpSecondaryIP + "</serverAddress>" + eol);
			}
			sb.append("                  <administrativeState>UNLOCKED</administrativeState>" + eol);
			sb.append("                </NtpServer>" + eol);
			sb.append("              </Ntp>" + eol);
			sb.append("            </TimeM>" + eol);
			sb.append("          </SysM>" + eol);
			sb.append("        </SystemFunctions>" + eol);
			sb.append("        <Transport>" + eol);
			sb.append("          <transportId>1</transportId>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_TRAFFIC</routerId>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);	
			sb.append("            <routerId>Node_Internal_F1</routerId>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("          <VlanPort xmlns=\"urn:com:ericsson:ecim:RtnL2VlanPort\">" + eol);
			sb.append("            <encapsulation>ManagedElement=1,Transport=1,EthernetPort=" + tnPort + "</encapsulation>" + eol);
			if((duInfo.tmoDUInfo.isLowBandMMBBVariation || duInfo.tmoDUInfo.isMidBandTddMMBBVariation || duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode()) && duInfo.is5G && !duInfo.isNRNodeLive) {
				sb.append("            <vlanId>" + duInfo.tmoDUInfo.gNodeBs1VlanId + "</vlanId>" + eol);
				sb.append("            <vlanPortId>" + duInfo.tmoDUInfo.gNodeBs1VlanId + "</vlanPortId>" + eol);
			}
			else {
				sb.append("            <vlanId>" + duInfo.s1VlanId + "</vlanId>" + eol);
				sb.append("            <vlanPortId>" + duInfo.s1VlanId + "</vlanPortId>" + eol);
			}
			sb.append("          </VlanPort>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_TRAFFIC</routerId>" + eol);
			sb.append("            <InterfaceIPv4 xmlns=\"urn:com:ericsson:ecim:RtnL3InterfaceIPv4\">" + eol);
			if((duInfo.tmoDUInfo.isLowBandMMBBVariation || duInfo.tmoDUInfo.isMidBandTddMMBBVariation || duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode()) && duInfo.is5G && !duInfo.isNRNodeLive) {
				sb.append("              <encapsulation>ManagedElement=1,Transport=1,VlanPort=" + duInfo.tmoDUInfo.gNodeBs1VlanId + "</encapsulation>" + eol);
			}else {
				sb.append("              <encapsulation>ManagedElement=1,Transport=1,VlanPort=" + duInfo.s1VlanId + "</encapsulation>" + eol);
			}
			sb.append("              <interfaceIPv4Id>1</interfaceIPv4Id>" + eol);
			sb.append("              <routesHoldDownTimer>180</routesHoldDownTimer>" + eol);
			sb.append("            </InterfaceIPv4>" + eol);
			sb.append("          </Router>" + eol);
			
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>Node_Internal_F1</routerId>" + eol);
			sb.append("            <InterfaceIPv4 xmlns=\"urn:com:ericsson:ecim:RtnL3InterfaceIPv4\">" + eol);
			sb.append("              <interfaceIPv4Id>NRCUCP</interfaceIPv4Id>" + eol);
			sb.append("              <loopback />" + eol);
			sb.append("            </InterfaceIPv4>" + eol);
			sb.append("            <InterfaceIPv4 xmlns=\"urn:com:ericsson:ecim:RtnL3InterfaceIPv4\">" + eol);
			sb.append("              <interfaceIPv4Id>NRDU</interfaceIPv4Id>" + eol);
			sb.append("              <loopback />" + eol);
			sb.append("            </InterfaceIPv4>" + eol);
			sb.append("          </Router>" + eol);

			subnetMask = "27";		// hard-coded default
			subnetMask = !duInfo.tmoDUInfo.gNodeBs1NetworkPrefixLength.isEmpty() ? duInfo.tmoDUInfo.gNodeBs1NetworkPrefixLength : subnetMask;	// [12162021] GMO_TMO-214
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_TRAFFIC</routerId>" + eol);
			sb.append("            <InterfaceIPv4 xmlns=\"urn:com:ericsson:ecim:RtnL3InterfaceIPv4\">" + eol);
			sb.append("              <interfaceIPv4Id>1</interfaceIPv4Id>" + eol);
			sb.append("              <AddressIPv4>" + eol);
			if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) {
				sb.append("                <address>" + duInfo.s1ControlPlaneIp + "/" + subnetMask + "</address>" + eol);		// /27
			}
			else if((duInfo.tmoDUInfo.isMidBandTddMMBBVariation) && duInfo.is5G && !duInfo.isNRNodeLive) {
				sb.append("                <address>" + duInfo.tmoDUInfo.gNodeBs1ControlPlaneIp + "/" + subnetMask + "</address>" + eol);		// /27
			}
			else if((duInfo.tmoDUInfo.isLowBandMMBBVariation || duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode()) && duInfo.is5G && !duInfo.isNRNodeLive) {
				if(duInfo.tmoDUInfo.isSASRouterTypeNSB) {
					sb.append("                <address>" + duInfo.tmoDUInfo.gNodeBs1ControlPlaneIp + "/" + subnetMask + "</address>" + eol);		// /29
				}else if(duInfo.tmoDUInfo.isIXRERouterTypeNSB || duInfo.tmoDUInfo.isExcalibur4G5GFDD) {
					sb.append("                <address>" + duInfo.tmoDUInfo.gNodeBs1ControlPlaneIp + "/" + subnetMask + "</address>" + eol);		// /27
				}
			}
			else if(duInfo.tmoDUInfo.isExcalibur4G5GFDD) {
				sb.append("                <address>" + duInfo.tmoDUInfo.gNodeBs1ControlPlaneIp + "/" + subnetMask + "</address>" + eol);		// /29
			}
			else {
				sb.append("                <address>" + duInfo.s1ControlPlaneIp + "/" + subnetMask + "</address>" + eol);		// /27
			}
			sb.append("                <addressIPv4Id>1</addressIPv4Id>" + eol);
			sb.append("              </AddressIPv4>" + eol);
			sb.append("            </InterfaceIPv4>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>Node_Internal_F1</routerId>" + eol);
			sb.append("            <InterfaceIPv4 xmlns=\"urn:com:ericsson:ecim:RtnL3InterfaceIPv4\">" + eol);
			sb.append("              <interfaceIPv4Id>NRCUCP</interfaceIPv4Id>" + eol);
			sb.append("              <AddressIPv4>" + eol);
			sb.append("                <address>169.254.42.42/32</address>" + eol);
			sb.append("                <addressIPv4Id>1</addressIPv4Id>" + eol);
			sb.append("              </AddressIPv4>" + eol);
			sb.append("            </InterfaceIPv4>" + eol);
			sb.append("            <InterfaceIPv4 xmlns=\"urn:com:ericsson:ecim:RtnL3InterfaceIPv4\">" + eol);
			sb.append("              <interfaceIPv4Id>NRDU</interfaceIPv4Id>" + eol);
			sb.append("              <AddressIPv4>" + eol);
			sb.append("                <address>169.254.42.43/32</address>" + eol);
			sb.append("                <addressIPv4Id>1</addressIPv4Id>" + eol);
			sb.append("              </AddressIPv4>" + eol);
			sb.append("            </InterfaceIPv4>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_OAM</routerId>" + eol);
			sb.append("            <RouteTableIPv4Static xmlns=\"urn:com:ericsson:ecim:RtnRoutesStaticRouteIPv4\">" + eol);
			sb.append("              <routeTableIPv4StaticId>1</routeTableIPv4StaticId>" + eol);
			sb.append("              <Dst>" + eol);
			sb.append("                <dst>0.0.0.0/0</dst>" + eol);
			sb.append("                <dstId>1</dstId>" + eol);
			sb.append("                <NextHop>" + eol);
			if((duInfo.tmoDUInfo.isLowBandMMBBVariation || duInfo.tmoDUInfo.isMidBandTddMMBBVariation || duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode()) && duInfo.is5G && !duInfo.isNRNodeLive) {
				sb.append("                  <address>" + duInfo.tmoDUInfo.gNodeBnmnetDefaultGateway + "</address>" + eol);
			}else {
				sb.append("                  <address>" + duInfo.nmnetDefaultGateway + "</address>" + eol);
			}
			sb.append("                  <adminDistance>10</adminDistance>" + eol);
			sb.append("                  <nextHopId>1</nextHopId>" + eol);
			sb.append("                </NextHop>" + eol);
			sb.append("              </Dst>" + eol);
			sb.append("            </RouteTableIPv4Static>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("          <Router xmlns=\"urn:com:ericsson:ecim:RtnL3Router\">" + eol);
			sb.append("            <routerId>vr_TRAFFIC</routerId>" + eol);
			sb.append("            <RouteTableIPv4Static xmlns=\"urn:com:ericsson:ecim:RtnRoutesStaticRouteIPv4\">" + eol);
			sb.append("              <routeTableIPv4StaticId>1</routeTableIPv4StaticId>" + eol);
			sb.append("              <Dst>" + eol);
			sb.append("                <dst>0.0.0.0/0</dst>" + eol);
			sb.append("                <dstId>1</dstId>" + eol);
			sb.append("                <NextHop>" + eol);
			if((duInfo.tmoDUInfo.isLowBandMMBBVariation || duInfo.tmoDUInfo.isMidBandTddMMBBVariation || duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode()) && duInfo.is5G && !duInfo.isNRNodeLive) {
				sb.append("                  <address>" + duInfo.tmoDUInfo.gNodeBcorenetDefaultGateway + "</address>" + eol);
			}else {
				sb.append("                  <address>" + duInfo.corenetDefaultGateway + "</address>" + eol);
			}
			sb.append("                  <adminDistance>10</adminDistance>" + eol);
			sb.append("                  <nextHopId>1</nextHopId>" + eol);
			sb.append("                </NextHop>" + eol);
			sb.append("              </Dst>" + eol);
			sb.append("            </RouteTableIPv4Static>" + eol);
			sb.append("          </Router>" + eol);
			sb.append("          <Synchronization xmlns=\"urn:com:ericsson:ecim:RsyncSynchronization\">" + eol);
			sb.append("            <synchronizationId>1</synchronizationId>" + eol);
			sb.append("            <RadioEquipmentClock xmlns=\"urn:com:ericsson:ecim:RsyncRadioEquipmentClock\">" + eol);
			sb.append("              <radioEquipmentClockId>1</radioEquipmentClockId>" + eol);
			sb.append("            </RadioEquipmentClock>" + eol);
			sb.append("          </Synchronization>" + eol);
			sb.append("        </Transport>" + eol);
			sb.append("        <Equipment xmlns=\"urn:com:ericsson:ecim:ReqEquipment\">" + eol);
			sb.append("          <equipmentId>1</equipmentId>" + eol);
			sb.append("          <FieldReplaceableUnit xmlns=\"urn:com:ericsson:ecim:ReqFieldReplaceableUnit\">" + eol);
			sb.append("            <fieldReplaceableUnitId>BB-01</fieldReplaceableUnitId>" + eol);
			sb.append("            <SyncPort xmlns=\"urn:com:ericsson:ecim:ReqSyncPort\">" + eol);
			sb.append("              <syncPortId>1</syncPortId>" + eol);
			sb.append("            </SyncPort>" + eol);
			sb.append("          </FieldReplaceableUnit>" + eol);
			sb.append("        </Equipment>" + eol);
			sb.append("        <Transport>" + eol);
			sb.append("          <transportId>1</transportId>" + eol);
			sb.append("          <Synchronization xmlns=\"urn:com:ericsson:ecim:RsyncSynchronization\">" + eol);
			sb.append("            <synchronizationId>1</synchronizationId>" + eol);
			if(!duInfo.tmoDUInfo.isMidBandAnchorScope && !duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio && !duInfo.tmoDUInfo.isMidBandTddMMBBVariation) {
				sb.append("            <TimeSyncIO xmlns=\"urn:com:ericsson:ecim:RsyncTimeSyncIO\">" + eol);
				sb.append("              <compensationDelay>0</compensationDelay>" + eol);
				sb.append("              <encapsulation>ManagedElement=1,Equipment=1,FieldReplaceableUnit=BB-01,SyncPort=1</encapsulation>" + eol);
				sb.append("              <timeSyncIOId>1</timeSyncIOId>" + eol);
				sb.append("            </TimeSyncIO>" + eol);
				sb.append("            <RadioEquipmentClock xmlns=\"urn:com:ericsson:ecim:RsyncRadioEquipmentClock\">" + eol);
				sb.append("              <radioEquipmentClockId>1</radioEquipmentClockId>" + eol);
				sb.append("              <RadioEquipmentClockReference>" + eol);
				sb.append("                <administrativeState>UNLOCKED</administrativeState>" + eol);
				sb.append("                <encapsulation>ManagedElement=1,Transport=1,Synchronization=1,TimeSyncIO=1</encapsulation>" + eol);
				sb.append("                <priority>1</priority>" + eol);
				sb.append("                <radioEquipmentClockReferenceId>1</radioEquipmentClockReferenceId>" + eol);
				if(duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) {
					sb.append("                <useQLFrom>RECEIVED_QL</useQLFrom>" + eol);
				}else {
					sb.append("                <useQLFrom>ADMIN_QL</useQLFrom>" + eol);
				}
				sb.append("                <adminQualityLevel>" + eol);
				sb.append("                  <qualityLevelValueOptionI>SSU_A</qualityLevelValueOptionI>" + eol);
				sb.append("                  <qualityLevelValueOptionII>STU</qualityLevelValueOptionII>" + eol);
				sb.append("                  <qualityLevelValueOptionIII>UNK</qualityLevelValueOptionIII>" + eol);
				sb.append("                </adminQualityLevel>" + eol);
				sb.append("              </RadioEquipmentClockReference>" + eol);
				sb.append("            </RadioEquipmentClock>" + eol);
				sb.append("            <TimeSyncIO xmlns=\"urn:com:ericsson:ecim:RsyncTimeSyncIO\">" + eol);
				sb.append("              <timeSyncIOId>1</timeSyncIOId>" + eol);
				sb.append("              <GnssInfo xmlns=\"urn:com:ericsson:ecim:RsyncGnssInfo\">" + eol);
				sb.append("                <gnssInfoId>1</gnssInfoId>" + eol);
				sb.append("              </GnssInfo>" + eol);
				sb.append("            </TimeSyncIO>" + eol);
			}
			sb.append("          </Synchronization>" + eol);
			sb.append("        </Transport>" + eol);
			sb.append("        <NodeSupport xmlns=\"urn:com:ericsson:ecim:RmeSupport\">" + eol);
			sb.append("          <nodeSupportId>1</nodeSupportId>" + eol);
			sb.append("          <ServiceDiscovery xmlns=\"urn:com:ericsson:ecim:RmeSds\">" + eol);
			sb.append("            <serviceDiscoveryId>1</serviceDiscoveryId>" + eol);
			
			sb.append("            <trustCategory>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,TrustCategory=oamTrustCategory</trustCategory>" + eol);
			sb.append("            <nodeCredential>ManagedElement=1,SystemFunctions=1,SecM=1,CertM=1,NodeCredential=oamNodeCredential</nodeCredential>" + eol);
			sb.append("            <primaryGsds>" + eol);
			sb.append("              <host>localhost</host>" + eol);
			sb.append("              <port>8301</port>" + eol);
			sb.append("              <serviceArea>NR</serviceArea>" + eol);
			sb.append("            </primaryGsds>" + eol);
			sb.append("          </ServiceDiscovery>" + eol);
			

			sb.append("        </NodeSupport>" + eol);
			sb.append("      </ManagedElement>" + eol);
			sb.append("    </config>" + eol);
			sb.append("  </edit-config>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"Closing\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <close-session></close-session>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<?xml version=\"1.0\" encoding=\"UTF-8\"?>" + eol);
			sb.append("<hello xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <capabilities>" + eol);
			sb.append("    <capability>urn:ietf:params:netconf:base:1.0</capability>" + eol);
			sb.append("  </capabilities>" + eol);
			sb.append("</hello>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"4\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <edit-config>" + eol);
			sb.append("    <target>" + eol);
			sb.append("      <running />" + eol);
			sb.append("    </target>" + eol);
			sb.append("    <config xmlns:xc=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("      <ManagedElement xmlns=\"urn:com:ericsson:ecim:ComTop\">" + eol);
			sb.append("        <managedElementId>1</managedElementId>" + eol);
			sb.append("        <networkManagedElementId>" + duInfo.duName + "</networkManagedElementId>" + eol);
			sb.append("      </ManagedElement>" + eol);
			sb.append("    </config>" + eol);
			sb.append("  </edit-config>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			sb.append("<rpc message-id=\"Closing\" xmlns=\"urn:ietf:params:xml:ns:netconf:base:1.0\">" + eol);
			sb.append("  <close-session></close-session>" + eol);
			sb.append("</rpc>" + eol);
			sb.append("]]>]]>" + eol);
			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate5GNRSiteBasicNetConf exception!", ex);
			Logger.getGmoLogger().printError("Error generating SiteBasic script! " + ex.getMessage());
		}

	}

	private Set<String> getAdditional5GSiteNamesFromTnd(Set<String> prmInitialSiteList)
	{
		Set<String> setFinalSiteList = new TreeSet<String>();
		String strBaseSiteName = prmInitialSiteList.toArray()[0].toString();
		// if the base site name ends with a number, trim it.
		if(strBaseSiteName.matches(".*[0-9]$")) {
			strBaseSiteName = strBaseSiteName.substring(0, strBaseSiteName.length() - 1);
		}

		// get all site names from the TND that match the trimmed site name pattern.
		ArrayList<String> lstMatchingSiteNames = CSVUtils.readDataArrayFromCSVFile(CSVUtils.getCIQCSVFile("ATND_GNODEB"), CiqConstants.ciqColumnStdToRegexMap.get("gNodeB Name"), strBaseSiteName + ".*", CiqConstants.ciqColumnStdToRegexMap.get("gNodeB Name"), false);
		if(lstMatchingSiteNames != null && lstMatchingSiteNames.size() > 0)
		{
			for(String strCurrSiteName : lstMatchingSiteNames)
			{
				// if this site is ALSO present in RND, ONLY THEN add it to the site list (Otherwise you end up getting a bunch of unnecessary errors because the site is in TND but not in RND)
				setFinalSiteList.add(strCurrSiteName);
			}
		}

		return setFinalSiteList;
	}

	private Set<String> sortSiteNames(Set<String> prmInitialSiteList)
	{
		Set<String> setFinalSiteList = new TreeSet<String>();
		for(String currSite : prmInitialSiteList){
			setFinalSiteList.add(currSite);
		}
		return setFinalSiteList;
	}

	public void generateCarrierAddCCScript01(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			String strGnbSecCarrPrefixToUse = "";

			for(Map.Entry<String, GNodeBSectorCarrierObj> kvp : duInfo.getgNodeBSectorCarrierMap().entrySet())
			{
				String strActualSecCarrierId = kvp.getValue().gNodeBSectorCarrierId;
				if(strActualSecCarrierId != null) {
					String [] arr = strActualSecCarrierId.split("-");
					if(arr.length == 3) {
						strGnbSecCarrPrefixToUse = arr[0] + "-" + arr[1];
						break;
					}
				}
			}

			sb.append("confl + " + eol);
			sb.append("gs+" + eol);
			sb.append(eol);
			sb.append("scw RP73:1" + eol);

			boolean blnIs4cc = false;
			// Loop through the cells and check if any of them have AIR 5331. If yes, its a 4CC site.
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {

				String strCurrCellFdd = kvp.getKey();

				String strCellEndingPattern = "^.*2$";

				// to support 2nd 3rd and 4th carriers
				strCellEndingPattern = "^.*[234]$";


				if(strCurrCellFdd.matches(strCellEndingPattern)) {
					SiteCellObj obCurrCellObj = kvp.getValue();

					// check the radioType
					if(StringUtil.doesMatch(obCurrCellObj.radioType, "AIR\\s*5331", 0)) {
						blnIs4cc = true;
						file = file.replace("_2CC_Add.mos", "_4CC_Add.mos");
						break;
					}
					else {
						blnIs4cc = false;
						break;
					}
				}
			}

			if(blnIs4cc)
			{
				sb.append("bl GNodeBRpFunction=1,GNodeBSectorCarrier=.*-01" + eol);
				sb.append("set GNodeBRpFunction=1,GNodeBSectorCarrier=.*-01 configuredMaxTxPower 250000" + eol);
				sb.append("deb GNodeBRpFunction=1,GNodeBSectorCarrier=.*-01" + eol);
			}
			else
			{
				sb.append("bl GNodeBRpFunction=1,GNodeBSectorCarrier=.*-01" + eol);
				sb.append("set GNodeBRpFunction=1,GNodeBSectorCarrier=.*-01 configuredMaxTxPower 80000" + eol);
				sb.append("deb GNodeBRpFunction=1,GNodeBSectorCarrier=.*-01" + eol);
			}

			
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String strCurrCellFdd = kvp.getKey();
				
				String strCellEndingPattern = "^.*2$";
				String strLastChar = strCurrCellFdd.substring(strCurrCellFdd.length() - 1);

				// to support 2nd 3rd and 4th carriers
				strCellEndingPattern = "^.*[234]$";

				if(strCurrCellFdd.matches(strCellEndingPattern)) {
					SiteCellObj obCurrCellObj = kvp.getValue();

					// check the radioType
					if(StringUtil.doesMatch(obCurrCellObj.radioType, "AIR\\s*5331", 0)) {
						blnIs4cc = true;
						file = file.replace("_2CC_Add.mos", "_4CC_Add.mos");
					}
					else {
						blnIs4cc = false;
					}

					sb.append(eol);
					sb.append(eol);
					sb.append("crn GNodeBRpFunction=1,TddRadioChannel=" + strLastChar + eol);
					sb.append("arfcn " + obCurrCellObj.earfcndl + eol);
					sb.append("channelBandwidth " + obCurrCellObj.channelBandwidth + eol);
					sb.append("end" + eol);
					sb.append(eol);
					sb.append("crn GNodeBRpFunction=1,GNodeBSectorCarrier=" + strGnbSecCarrPrefixToUse + "-0" + strLastChar + eol);
					sb.append("administrativeState 1" + eol);
					if(blnIs4cc) {
						sb.append("configuredMaxTxPower 250000" + eol);
					}
					else {
						sb.append("configuredMaxTxPower 80000" + eol);
					}
					sb.append("radioChannelDuplexingRef GNodeBRpFunction=1,TddRadioChannel=" + strLastChar + eol);
					sb.append("sectorEquipmentFunctionRef SectorEquipmentFunction=" + strGnbSecCarrPrefixToUse + eol);
					sb.append("end" + eol);
					sb.append(eol);
					sb.append("crn GNodeBFunction=1,GUtranCell=" + strCurrCellFdd + eol);
					sb.append("administrativeState 1" + eol);
					sb.append("cellId " + obCurrCellObj.cellId + eol);
					sb.append("tempTac " + duInfo.tac + eol);
					sb.append("end" + eol);
					sb.append(eol);

					sb.append("crn GNodeBRpFunction=1,GUtranDUCell=" + strCurrCellFdd + eol);

					sb.append("administrativeState 0" + eol);

					sb.append("bandListManual 261" + eol);

					sb.append("cgi " + obCurrCellObj.nCGI + eol);
					sb.append("gNodeBSectorCarrierRef GNodeBRpFunction=1,GNodeBSectorCarrier=" + strGnbSecCarrPrefixToUse + "-0" + strLastChar + eol);
					sb.append("pZeroNomPucch -96" + eol);
					sb.append("pZeroNomPuschGrant -90" + eol);
					sb.append("physicalLayerCellIdGroup " + obCurrCellObj.physicalLayerCellIdGroup + eol);
					sb.append("physicalLayerSubCellId " + obCurrCellObj.physicalLayerSubCellId + eol);
					sb.append("tempTac " + duInfo.tac + eol);
					sb.append("end" + eol);

				}
			}
			sb.append(eol);
			sb.append(eol);
			sb.append("wait 2" + eol);
			sb.append(eol);

			if(blnIs4cc)
			{
				sb.append("cr FieldReplaceableUnit=" + strGnbSecCarrPrefixToUse + ",RiPort=DATA_3" + eol);
				sb.append("cr FieldReplaceableUnit=" + strGnbSecCarrPrefixToUse + ",RiPort=DATA_4" + eol);

				sb.append("crn Equipment=1,RiLink=BB-01-C-" + strGnbSecCarrPrefixToUse + "-Data3" + eol);
				sb.append("fronthaulDeviceLineRate 0" + eol);
				sb.append("riPortRef1 FieldReplaceableUnit=BB-01,RiPort=C" + eol);
				sb.append("riPortRef2 FieldReplaceableUnit=" + strGnbSecCarrPrefixToUse + ",RiPort=DATA_3" + eol);
				sb.append("transportType 0" + eol);
				sb.append("end" + eol);
				sb.append(eol);

				sb.append("crn Equipment=1,RiLink=BB-01-D-" + strGnbSecCarrPrefixToUse + "-Data4" + eol);
				sb.append("fronthaulDeviceLineRate 0" + eol);
				sb.append("riPortRef1 FieldReplaceableUnit=BB-01,RiPort=D" + eol);
				sb.append("riPortRef2 FieldReplaceableUnit=" + strGnbSecCarrPrefixToUse + ",RiPort=DATA_4" + eol);
				sb.append("transportType 0" + eol);
				sb.append("end" + eol);

			}

			sb.append("gs-" + eol);
			sb.append("confb-" + eol);

			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate2CCScript01 exception!", ex);
			Logger.getGmoLogger().printError("Error generating 5G Carrier Add 01 script! " + ex.getMessage());
		}
	}

	public void generateCarrierAddCCScript01_MTR1921(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			String strGnbSecCarrPrefixToUse = "";
			for(Map.Entry<String, GNodeBSectorCarrierObj> kvp : duInfo.getgNodeBSectorCarrierMap().entrySet())
			{
				String strActualSecCarrierId = kvp.getValue().gNodeBSectorCarrierId;
				if(strActualSecCarrierId != null) {
					String [] arr = strActualSecCarrierId.split("-");
					if(arr.length == 3) {
						strGnbSecCarrPrefixToUse = arr[0] + "-" + arr[1];
						break;
					}
				}
			}
			
			if(strGnbSecCarrPrefixToUse.length() < 4) {
				for(Map.Entry<String, SectorEquipmentFunctionObj> kvp : duInfo.getSectorEquipmentFunctionMap().entrySet()) {
					SectorEquipmentFunctionObj secEquipFuncObj = kvp.getValue();
					strGnbSecCarrPrefixToUse = secEquipFuncObj.getSectorEquipmentFunctionId();
				}
			}
			// calculate the value of rachRootSequence for this site.
			String strRachRootSequenceForThisSite = "";
			try {
				if(strGnbSecCarrPrefixToUse.length() > 3 && strGnbSecCarrPrefixToUse.contains("-")) {
					// split the secCarrierPrefixToUse and get only the second part (after the '-')
					String [] arrSplitItems = strGnbSecCarrPrefixToUse.split("-");

					// convert that second part to an int
					if(arrSplitItems.length >= 2) {
						int secondPart = Integer.parseInt(arrSplitItems[1]);
						
						// multiply (second-part minus 1) with 32. The resultant number is the value to be used for rachRootSequence for this site
						strRachRootSequenceForThisSite = String.valueOf((secondPart - 1) * 32);
					}
				}
			}
			catch(Exception ex) {
				strRachRootSequenceForThisSite = "";
			}

			String configuredMaxTxPowerValueToBeUsed = "250000";
			
			// determine what configuredMaxTxPower value to be used based on the Radio Type of the cell.
			// Loop through the cells and check if any of them have AIR 5331. 

			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {

				String strCurrCellFdd = kvp.getKey();
				
				String strCellEndingPattern = "^.*2$";

				// to support 2nd 3rd and 4th carriers
				strCellEndingPattern = "^.*[234]$";

				if(strCurrCellFdd.matches(strCellEndingPattern)) {
					SiteCellObj obCurrCellObj = kvp.getValue();

					// check the radioType
					if(StringUtil.doesMatch(obCurrCellObj.radioType, "AIR\\s*5331", 0)) {
						configuredMaxTxPowerValueToBeUsed = "250000";
						break;
					}
					else if(StringUtil.doesMatch(obCurrCellObj.radioType, "AIR\\s*5121", 0)) {
						configuredMaxTxPowerValueToBeUsed = "80000";
						break;
					} 
					else {
						configuredMaxTxPowerValueToBeUsed = "1";
						break;
					}
				}
			}

			sb.append("confl + " + eol);
			sb.append("gs+" + eol);
			sb.append(eol);
			sb.append("bl GNBDUFunction=1,NRSectorCarrier=.*-01" + eol);
			sb.append("set GNBDUFunction=1,NRSectorCarrier=.*-01 configuredMaxTxPower " + configuredMaxTxPowerValueToBeUsed + eol);
			sb.append("deb GNBDUFunction=1,NRSectorCarrier=.*-01" + eol);
			sb.append(eol);

			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String strCurrCellFdd = kvp.getKey();

				String strCellEndingPattern = "^.*2$";
				
				// [eshinai: 070119]
				// To support only 2nd carrier due to current SW Limitation.
				// Later on this will be updated to allow all sectors.
				strCellEndingPattern = "^.*[2]$";

				if(strCurrCellFdd.matches(strCellEndingPattern)) {
					SiteCellObj obCurrCellObj = kvp.getValue();
					String strBandWidthDividedBy1000 = "";
					try	{
						strBandWidthDividedBy1000 = String.valueOf(Integer.parseInt(obCurrCellObj.channelBandwidth) / 1000);
					}
					catch(Exception ex)	{
						strBandWidthDividedBy1000 = "";
					}

					sb.append("crn GNBDUFunction=1,NRSectorCarrier=" + strGnbSecCarrPrefixToUse + "-02" + eol);
					sb.append("administrativeState 1" + eol);
					sb.append("arfcnDL " + obCurrCellObj.earfcndl + eol);
					sb.append("arfcnUL " + obCurrCellObj.earfcnul + eol);
					sb.append("bSChannelBwDL " + strBandWidthDividedBy1000 + eol);
					sb.append("bSChannelBwUL " + strBandWidthDividedBy1000 + eol);
					sb.append("configuredMaxTxPower " + configuredMaxTxPowerValueToBeUsed + eol);
					sb.append("sectorEquipmentFunction SectorEquipmentFunction=" + strGnbSecCarrPrefixToUse + eol);
					sb.append("txDirection 1" + eol);
					sb.append("end" + eol);
					sb.append(eol);
					sb.append("crn GNBCUCPFunction=1,NRCellCU=" + strCurrCellFdd + eol);
					sb.append("cellLocalId " + obCurrCellObj.cellId + eol);
					sb.append("end" + eol);
					sb.append(eol);
					sb.append("crn GNBDUFunction=1,NRCellDU=" + strCurrCellFdd + eol);
					sb.append("administrativeState 0" + eol);
					sb.append("cellLocalId " + obCurrCellObj.cellId + eol);
					sb.append("nCI " + obCurrCellObj.nCI + eol);
					sb.append("nRPCI " + obCurrCellObj.pci + eol);
					sb.append("nRSectorCarrier GNBDUFunction=1,NRSectorCarrier=" + strGnbSecCarrPrefixToUse + "-02" + eol);
					sb.append("nRTAC " + duInfo.tac + eol);
					sb.append("pLMNIdList mcc=310,mnc=260" + eol);

					// #TC_188

					sb.append("rachRootSequence " + strRachRootSequenceForThisSite + eol);


					sb.append("end" + eol);
					sb.append(eol);

					// #TC_188

					sb.append("wait 5" + eol);
					sb.append(eol);


					sb.append("set NRCellDU=" + strCurrCellFdd + ",RandomAccess=1 rachRootSequence " + strRachRootSequenceForThisSite + eol);
					sb.append(eol);
					sb.append("crn GNBDUFunction=1,NRCellDU=" + strCurrCellFdd + ",SyncSignal=1" + eol);
					sb.append("blockPerBurstSet 12" + eol);
					sb.append("ssbFirstSymbolIndex 3" + eol);
					sb.append("ssbPeriodicity 20" + eol);
					sb.append("ssbPosition 0" + eol);
					sb.append("end" + eol);

				}
			}
			sb.append(eol);
			sb.append("wait 2" + eol);
			sb.append(eol);
			
			sb.append("gs-" + eol);
			sb.append("confb-" + eol);

			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate2CCScript01 exception!", ex);
			Logger.getGmoLogger().printError("Error generating 5G Carrier Add 01 script! " + ex.getMessage());
		}
	}

	public void generateCarrierAddCCScript02(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try
		{
			boolean blnIs4cc = false;
			sb.append("lt all" + eol);
			sb.append(eol);
			sb.append("confb+" + eol);
			sb.append("gs+" + eol);
			sb.append(eol);
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String strCurrCellFdd = kvp.getKey();

				String strCellEndingPattern = "^.*[234]$";
				String strLastCharOfCellFdd = strCurrCellFdd.substring(strCurrCellFdd.length() - 1);
				String strSecondToLastChar = strCurrCellFdd.substring(strCurrCellFdd.length() - 2, strCurrCellFdd.length() - 1);

				// to support 2nd 3rd and 4th carriers
				strCellEndingPattern = "^.*[234]$";

				if(strCurrCellFdd.matches(strCellEndingPattern)) {
					SiteCellObj obCurrCellObj = kvp.getValue();
						// check the radioType
						if(StringUtil.doesMatch(obCurrCellObj.radioType, "AIR\\s*5331", 0)) {
							blnIs4cc = true;
						}
						else {
							blnIs4cc = false;
						}

					if(blnIs4cc) {
						sb.append("get GNodeBFunction=1,GUtranCell=.*" + strSecondToLastChar + strLastCharOfCellFdd + "$ cgi > $cgiValue" + strSecondToLastChar + strLastCharOfCellFdd + eol);
					}
					else {
						sb.append("get GNodeBFunction=1,GUtranCell=.*" + strLastCharOfCellFdd + "$ cgi > $cgiValue12" + eol);
					}
				}
			}
			sb.append(eol);
			for(Map.Entry<String, SiteCellObj> kvp : duInfo.newCellToCellInfo.entrySet()) {
				String strCurrCellFdd = kvp.getKey();

				String strCellEndingPattern = "^.*[234]$";
				String strLastCharOfCellFdd = strCurrCellFdd.substring(strCurrCellFdd.length() - 1);
				String strSecondToLastChar = strCurrCellFdd.substring(strCurrCellFdd.length() - 2, strCurrCellFdd.length() - 1);

				if(strCurrCellFdd.matches(strCellEndingPattern)) {
					if(blnIs4cc) {
						sb.append("set GNodeBRpFunction=1,GUtranDUCell=.*" + strLastCharOfCellFdd + "$ cgi $cgiValue" + strSecondToLastChar + strLastCharOfCellFdd + eol);
					}
					else{
						sb.append("set GNodeBRpFunction=1,GUtranDUCell=.*" + strLastCharOfCellFdd + "$ cgi $cgiValue12" + eol);
					}
				
				}
			}

			sb.append(eol);
			sb.append("confb-" + eol);
			sb.append("gs-" + eol);

			FileUtil.writeToFile(sb, file);
		}
		catch(Exception ex)
		{
			Logger.logger.error("generate2CCScript02 exception!", ex);
			Logger.getGmoLogger().printError("Error generating 5G Carrier Add 02 script! " + ex.getMessage());
		}
	}
	
	/**
	 * Function to generate IntraFreq - InterGnb- relation
	 * @return
	 */
	protected void generateIntraFreqInterGnbRelationScript(SiteCellObj duInfo, StringBuilder sbHeader, String file, String eolType) 
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();
		HashMap<String,String> CellTocellPriority=new HashMap<>();
		ArrayList<String> NRCellDUIdList = new ArrayList<String>();
		List<HashMap<String, String>> gUtranCellMapList = new ArrayList<HashMap<String, String>>();
		boolean nrTwoCarrier= false;
		boolean changeForMmbb = (duInfo.tmoDUInfo.isMMBBNode && duInfo.isNRNodeLive && !duInfo.tmoDUInfo.isTDDMixedModeBaseBandScope && !duInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope) ? true : false;	// [06092020] Subtle changes for MMBB, may eventually be applied for all scopes
		boolean changeForMMBBNSB = (((duInfo.tmoDUInfo.isMixedModeBasebandScope && !(duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) || duInfo.tmoDUInfo.isLowBandMMBBVariation|| duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode() || duInfo.tmoDUInfo.isLowBandSetUp1DReconfig) && !duInfo.isNRNodeLive && duInfo.is5G) ? true : false ; //[07212020] Changes required when NR is NSB
		boolean changeforN41 = ((duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) && !duInfo.tmoDUInfo.isMMBBNode) ? true : false; // 12-11-2020 add "Pr" Command for N41 Node
		boolean changeforTDDMMBB = ((duInfo.tmoDUInfo.isTDDMixedModeBaseBandScope || duInfo.tmoDUInfo.isMidBandTddMMBBVariation) && !duInfo.isNRNodeLive && duInfo.is5G) ? true : false; 	// TDD MMBB Var3
		boolean changeforTDD2cAdd = (duInfo.tmoDUInfo.isTddCarrierAddScope && duInfo.isNRNodeLive && duInfo.is5G) ? true : false; 														// [12082021] GMO_TMO-206
		boolean changeforTDD1c2cNSBAdd = (duInfo.tmoDUInfo.isTddCarrierAddScope && duInfo.tmoDUInfo.isMidBandTdd1C2CN41AddScope && duInfo.isNewSite && duInfo.is5G) ? true : false; 		// [01132022] GMO_TMO-215
		
		try 
		{	
			sb = sbHeader;			// [06092020] Optional header
			sb.append("Confbdl+" + eol);

			if(changeforTDDMMBB || changeforN41) {
				if(duInfo.nodeBandType.equals("N41") && StringUtil.doesElementMatch(duInfo.tmoDUInfo.radioTypeSet, ".*6488.*", Pattern.CASE_INSENSITIVE)) {
					sb.append(eol);
					sb.append("setm NRCellDU csiRsConfig16P csiRsControl16Ports=0,i11Restriction=,i12Restriction= csiRsConfig2P csiRsControl2Ports=0,aRestriction= csiRsConfig32P csiRsControl32Ports=2,i11Restriction=FFFF,i12Restriction=FFFF csiRsConfig4P csiRsControl4Ports=0,i11Restriction= csiRsConfig8P csiRsControl8Ports=1,i11Restriction=FFFF,i12Restriction=" + eol);
					sb.append(eol);
				}
			}

			sb.append("gs+" + eol);
			sb.append(eol);
			sb.append("lt all" + eol);
			sb.append(eol);
			if ((!changeForMmbb && !changeForMMBBNSB) || changeforTDDMMBB || changeforN41 || changeforTDD2cAdd || changeforTDD1c2cNSBAdd) {
				sb.append("$date = `date +%y%m%d-%H%M`" + eol);
				sb.append("cvmk CV_pre_NRIntra_relation_$date" + eol);
				sb.append(eol);
			}
			sb.append("unset all" + eol);
			sb.append(eol);
			if(duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
				sb.append("pr NRCellDU=" + eol);
				sb.append("if $nr_of_mos != 0" + eol);
				sb.append("deb NRCellDU=" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
			}
			if((changeForMMBBNSB && !changeforTDDMMBB)) {
				sb.append("set NRCellDU=.*1$ ssbFrequency 0" + eol);
			}
			else if(changeforTDD2cAdd || changeforTDD1c2cNSBAdd
					|| changeforTDDMMBB) {						// [02092022] GMO_TMO-237
				if(!duInfo.tmoDUInfo.isExcalibur4G5GTDD)
				sb.append("deb NRCellDU" + eol+ eol);
				sb.append("WAIT 30" + eol);
			}
			sb.append(eol);
			sb.append("mr unlockedcell" + eol);
			if (!changeforTDD2cAdd && !changeforTDD1c2cNSBAdd
					&& !changeforTDDMMBB) {						// [02092022] GMO_TMO-237
				sb.append("ma unlockedcell NRCellDU=.*1$ administrativestate 1" + eol);
			}
			else {
				sb.append("ma unlockedcell NRCellDU administrativestate 1" + eol);
			}
			sb.append("bl unlockedcell" + eol);
			sb.append("WAIT 5" + eol);
			sb.append(eol);
			if(changeforTDD2cAdd || changeforTDD1c2cNSBAdd		// [12082021] GMO_TMO-206
				|| changeforTDDMMBB) {							// [02092022] GMO_TMO-237
				sb.append(genericScriptBlockGenerator.generateSingleLineComment("N41 1C 3sec"));
			}
			else {
				sb.append(eol);
				sb.append(eol);
			}
			if (!changeForMmbb || changeforTDD2cAdd || changeforTDD1c2cNSBAdd) {
				sb.append("get GNBDUFunction=1,NRCellDU=.*1$ ssbFrequencyAutoSelected > $ssbarfcn" + eol);
			}
//			else if (changeforTDD1c2cNSBAdd) {			// [01172022] GMO_TMO-215
//				sb.append("get GNBDUFunction=1,NRCellDU= ssbFrequencyAutoSelected > $ssbarfcn" + eol);
//			}
			if(duInfo.tmoDUInfo.isExcaliburSmallCellSite) {
				sb.append("mr variablessb" + eol);
				sb.append("ma variablessb GNBDUFunction=1,NRCellDU= ssbFrequencyAutoSelected !^$" + eol);
				sb.append(eol);
				sb.append(eol);
				sb.append("pr variablessb" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("print Exiting !!!!!!!!!! ABORT due to NR cell not unlocked!!!!!!!!!!" + eol);
				sb.append("return" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("$ssbarfcn = null" + eol);
				sb.append("$NRFreqid = null" + eol);
				sb.append("get variablessb ssbFrequencyAutoSelected > $ssbarfcn" + eol);
			}
			if (changeForMmbb && !changeforTDD2cAdd && !changeforTDD1c2cNSBAdd
					&& !changeforTDDMMBB) {				// [02092022] GMO_TMO-237
				Map<String, NRCellObj> nrCellMap = new TreeMap<String, NRCellObj>(duInfo.getNrSiteObj().getnRCellMap());
				for(Entry<String, NRCellObj> kvp : nrCellMap.entrySet()) {
					String currCellFddName = kvp.getKey();
					String cellNumber = currCellFddName.substring(currCellFddName.length()-2);
					String lastSecondDigit = currCellFddName.substring(currCellFddName.length() - 2, currCellFddName.length() - 1);
					String nrCellDUId = "id_NRCellDU" + lastSecondDigit;
					if(!NRCellDUIdList.contains(nrCellDUId)) {
						NRCellDUIdList.add(nrCellDUId);
					}
					sb.append("get GNBDUFunction=1,NRCellDU=.*" + cellNumber + "$ NRCellDUId > $" + nrCellDUId + eol);
				}
			}
			else {
				if(duInfo.tmoDUInfo.isExcalibur4G5GFDD && duInfo.tmoDUInfo.hasExcalibur4OrMoreSectors) {
					Map<String, NRCellObj> nrCellMap = new TreeMap<String, NRCellObj>(duInfo.getNrSiteObj().getnRCellMap());
					for(Entry<String, NRCellObj> kvp : nrCellMap.entrySet()) {
						String currCellFddName = kvp.getKey();
						String cellNumber = currCellFddName.substring(currCellFddName.length()-2);
						String lastSecondDigit = currCellFddName.substring(currCellFddName.length() - 2, currCellFddName.length() - 1);
						String nrCellDUId = "id_NRCellDU" + lastSecondDigit;
						String cellPriority=CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_NR2NRFREQRELATION"), "NRFreqRelation",currCellFddName, "cellReselectionPriority");
						if(cellPriority != null && cellPriority != "") {
							CellTocellPriority.put(nrCellDUId, cellPriority);
						}
						if(!NRCellDUIdList.contains(nrCellDUId)) {
							NRCellDUIdList.add(nrCellDUId);
						}
						sb.append("get GNBDUFunction=1,NRCellDU=.*" + cellNumber + "$ NRCellDUId > $" + nrCellDUId + eol);
					}
				}
				else {
					Map<String, SiteCellObj> newCellInfoMap = new TreeMap<String, SiteCellObj>(duInfo.newCellToCellInfo);
					for(Map.Entry<String, SiteCellObj> kvp : newCellInfoMap.entrySet()) {
						String currCellFddName = kvp.getKey();
						if(!currCellFddName.matches("^[DETVXW].*")) {
							if(duInfo.tmoDUInfo.getIsStandAloneLowBandMmbbNode() || duInfo.tmoDUInfo.isLowBandSetUp1DReconfig) {
								if(!currCellFddName.matches("^[KA].*")) {
									continue;
								}
							}

							String cellNumber = currCellFddName.substring(currCellFddName.length()-2);
							String lastSecondDigit = currCellFddName.substring(currCellFddName.length() - 2, currCellFddName.length() - 1);
							String lastDigit = currCellFddName.substring(currCellFddName.length() - 1, currCellFddName.length());		// [12082021] GMO_TMO-206
							if(duInfo.tmoDUInfo.isExcaliburSmallCellSite && !currCellFddName.startsWith("A")) {
								continue;
							}
							String nrCellDUId = "id_NRCellDU" + lastSecondDigit;

							if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd		// [12082021] GMO_TMO-206
								|| changeforTDDMMBB) {							// [02092022] GMO_TMO-237
								nrCellDUId = "id_NRCellDU" + lastSecondDigit + lastDigit;
								if (!lastDigit.contentEquals("1"))				// Do not continue if 2nd carrier cell
									continue;
							}
							
							if(duInfo.tmoDUInfo.isExcalibur4G5GFDD) {

								String cellPriority=CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_NR2NRFREQRELATION"), "NRFreqRelation", currCellFddName, "cellReselectionPriority");
								if(cellPriority!=null && cellPriority!="") {
									CellTocellPriority.put(nrCellDUId, cellPriority);
								}
								if(!NRCellDUIdList.contains(nrCellDUId)) {
									NRCellDUIdList.add(nrCellDUId);
									if(cellNumber.endsWith("1")) {
										sb.append("get GNBDUFunction=1,NRCellDU=.*" + cellNumber + "$ NRCellDUId > $" + nrCellDUId + eol);
									}
								}
							}
							else {
								if(!NRCellDUIdList.contains(nrCellDUId)) {
									NRCellDUIdList.add(nrCellDUId);
								}
								sb.append("get GNBDUFunction=1,NRCellDU=.*" + cellNumber + "$ NRCellDUId > $" + nrCellDUId + eol);
							}
						}
					}
				}
			}

			if(duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD
					|| changeforTDD2cAdd  || changeforTDD1c2cNSBAdd				// [12082021] GMO_TMO-206
					|| changeforTDDMMBB)	{									// [02102022] GMO_TMO-237
				Map<String, NRCellObj> nrCellMap = new TreeMap<String, NRCellObj>(duInfo.getNrSiteObj().getnRCellMap());
				for(Entry<String, NRCellObj> kvp : nrCellMap.entrySet()) {
					String currCellFddName = kvp.getKey();
					String cellNumber = currCellFddName.substring(currCellFddName.length()-2);
					if(currCellFddName.startsWith("K") && currCellFddName.endsWith("1")) {
						sb.append(eol);
						sb.append("get GNBDUFunction=1,NRCellDU=.*" + cellNumber + "$ nCI > $id_nci_NRCellDU" + cellNumber + eol);
						sb.append("$id_nci_NRCellDU" + cellNumber + " = auto$id_nci_NRCellDU" + cellNumber + eol);
					}
					else if(currCellFddName.startsWith("A") && (currCellFddName.endsWith("1"))) {
						sb.append(eol);
						sb.append("get GNBDUFunction=1,NRCellDU=.*" + cellNumber + "$ nCI > $id_nci_NRCellDU" + cellNumber + eol);
						sb.append("$id_nci_NRCellDU" + cellNumber + " = auto$id_nci_NRCellDU" + cellNumber + eol);
					}
				}
			}

			sb.append(eol);
			sb.append(eol);
			sb.append(genericScriptBlockGenerator.generateNRNetworkGenericBlock(duInfo));
			sb.append(eol);
			if (changeForMmbb && !changeforTDD2cAdd && !changeforTDD1c2cNSBAdd) {
				String ssbarfcn = "";
				String nrFreqid = "";
				String existingduName = "";
				if(duInfo.tmoDUInfo.isMMBBNode && !duInfo.getNrSiteObj().getgNBDUNameOld().isEmpty() && !duInfo.duName.contentEquals(duInfo.getNrSiteObj().getgNBDUNameOld())) {
					existingduName = duInfo.getNrSiteObj().getgNBDUNameOld();
				}
				for (HashMap<String, String> cellRowData : CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getKGETCSVFile("NRCellDU"), "NodeMOKey", existingduName + "!.*")) {
					String nrCellDUId = CommonUtil.getValueFromRegexKey(cellRowData, "NRCellDUId");
					String administrativeState = CommonUtil.getValueFromRegexKey(cellRowData, "administrativeState");
					administrativeState = administrativeState.replaceAll("[\\D]", "");
					String ssbFrequencyAutoSelected = CommonUtil.getValueFromRegexKey(cellRowData, "ssbFrequencyAutoSelected");
					if(!nrCellDUId.isEmpty() && administrativeState.contentEquals("1") && !ssbFrequencyAutoSelected.isEmpty()) {
						ssbarfcn = ssbFrequencyAutoSelected;
						nrFreqid = ssbarfcn + "-15-20-0-1";
					}
				}
				sb.append("$ssbarfcn = " + ssbarfcn + eol);
				sb.append("$NRFreqid = " + nrFreqid + eol);
			}
			else if(changeForMMBBNSB) {
				if(duInfo.tmoDUInfo.isExcaliburSmallCellSite) {
					sb.append("$NRFreqid = $ssbarfcn-30-20-0-1" + eol);
				}else {
					sb.append("$NRFreqid = $ssbarfcn-15-20-0-1" + eol);
				}
				sb.append(eol);
				sb.append("pr GNBCUCPFunction=1,NRNetwork=1,NRFrequency=$NRFreqid$" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1,NRNetwork=1,NRFrequency=$NRFreqid" + eol);
				sb.append("arfcnValueNRDl  $ssbarfcn" + eol);
				sb.append("smtcDuration 1" + eol);
				sb.append("smtcOffset 0" + eol);
				sb.append("smtcPeriodicity 20" + eol);
				if(duInfo.tmoDUInfo.isExcaliburSmallCellSite) {
					sb.append("smtcScs 30" + eol);
				}else {
					sb.append("smtcScs 15" + eol);
				}
				sb.append("end" + eol);
				sb.append("fi" + eol);
			}
			else {
				if(duInfo.isNR600) {
					sb.append("$NRFreqid = $ssbarfcn-15-20-0-1" + eol);
				}else {
					sb.append("$NRFreqid = $ssbarfcn-30-20-0-1" + eol);
				}
				sb.append(eol);

				if(changeforN41 || changeforTDDMMBB || changeforTDD2cAdd || changeforTDD1c2cNSBAdd)	{	// 12-11-2020 pr command addition cont'd, [12082021] GMO_TMO-206
					sb.append("pr GNBCUCPFunction=1,NRNetwork=1,NRFrequency=$NRFreqid$" + eol);
					sb.append("if $nr_of_mos = 0" + eol);	
				}

				sb.append("crn GNBCUCPFunction=1,NRNetwork=1,NRFrequency=$NRFreqid" + eol);
				sb.append("arfcnValueNRDl  $ssbarfcn" + eol);
				sb.append("smtcDuration 1" + eol);
				sb.append("smtcOffset 0" + eol);
				sb.append("smtcPeriodicity 20" + eol);
				if(duInfo.isNR600) {
					sb.append("smtcScs 15" + eol);
				}else {
					sb.append("smtcScs 30" + eol);
				}
				sb.append("end" + eol);
				if(changeforN41 || changeforTDDMMBB || duInfo.tmoDUInfo.isExcalibur4G5GFDD || changeforTDD2cAdd || changeforTDD1c2cNSBAdd){// 12-11-2020 pr command addition cont'd, [12082021] GMO_TMO-206
					sb.append("fi" + eol);	
				}
			}

			sb.append(eol);

			Collections.sort(NRCellDUIdList);

			for(String nrCellDUId : NRCellDUIdList) {
				sb.append("pr GNBCUCPFunction=1,NRCellCU=$" + nrCellDUId + ",NRFreqRelation=$ssbarfcn" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1,NRCellCU=$" + nrCellDUId + ",NRFreqRelation=$ssbarfcn" + eol);
				if (duInfo.tmoDUInfo.isExcalibur4G5GFDD) {
					if (duInfo.tmoDUInfo.isExcaliburSmallCellSite) {
						sb.append("cellReselectionPriority 7" + eol);
					} else {
						sb.append("cellReselectionPriority " + CellTocellPriority.get(nrCellDUId) + eol);
					}
				}else {
					String cellReselectionPriority = "7";
					if(!duInfo.tmoDUInfo.hasExcalibur4G5G) {
						String sourceBand = duInfo.nodeBandType.toUpperCase();
						String targetBand = duInfo.nodeBandType.toUpperCase();
						cellReselectionPriority = TMO_CommonUtil.calculateMarketSpecficCellReselectionPriorityValue(duInfo, sourceBand, targetBand, cellReselectionPriority);
					}					
					sb.append("cellReselectionPriority " + cellReselectionPriority + eol);
				}
				sb.append("nRFrequencyRef NRNetwork=1,NRFrequency=$NRFreqid" + eol);
				sb.append("pMax 23" + eol);
				sb.append("qOffsetFreq 0" + eol);
				sb.append("qQualMin " + eol);
				sb.append("qRxLevMin -140" + eol);
				sb.append("sIntraSearchP 62" + eol);
				sb.append("sIntraSearchQ " + eol);
				sb.append("tReselectionNR 2" + eol);
				sb.append("threshXHighP 4" + eol);
				sb.append("threshXHighQ " + eol);
				sb.append("threshXLowP 0" + eol);
				sb.append("threshXLowQ " + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
			}

			//NR CellRelation
			ArrayList<String> NRCellRelationIdList = new ArrayList<String>();
			ArrayList<String> temp = NRCellDUIdList;
			for(int i=0; i<temp.size(); i++) {
				String currNRCellDUId = temp.get(i);
				for(int j=0; j<NRCellDUIdList.size(); j++) {
					if(NRCellDUIdList.get(j) != temp.get(i)) {
						NRCellRelationIdList.add(NRCellDUIdList.get(j));
					}
				}
				for(String nrCellRelationId: NRCellRelationIdList) {
					if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd//) {     	// [12092021] GMO_TMO-206
							|| changeforTDDMMBB) {								// [02092022] GMO_TMO-237
						String nrCellRelationId1 = nrCellRelationId;
						StringBuilder nrCellRelationsb = new StringBuilder(nrCellRelationId1);
						nrCellRelationsb.insert(3, "nci_");
						sb.append("pr GNBCUCPFunction=1,NRCellCU=$" + currNRCellDUId + ",NRCellRelation=$" + nrCellRelationId + eol);
						sb.append("$id = $nr_of_mos" + eol);
						sb.append("pr GNBCUCPFunction=1,NRCellCU=$" + currNRCellDUId + ",NRCellRelation=$" + nrCellRelationsb + eol);
						sb.append("$id1 = $nr_of_mos" + eol);
						sb.append("if $id = 0 && $id1 = 0" + eol);
					}
					else {
						if(duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
							String nrCellRelationId1 = nrCellRelationId;
							StringBuilder nrCellRelationsb = new StringBuilder(nrCellRelationId1);
							nrCellRelationsb.insert(3, "nci_");
							sb.append("pr GNBCUCPFunction=1,NRCellCU=$" + currNRCellDUId + ",NRCellRelation=$" + nrCellRelationsb + "1" + eol);
						}else {
							sb.append("pr GNBCUCPFunction=1,NRCellCU=$" + currNRCellDUId + ",NRCellRelation=$" + nrCellRelationId + eol);
						}
						sb.append("if $nr_of_mos = 0" + eol);
					}

					if(duInfo.tmoDUInfo.isExcalibur4G5GFDD || duInfo.tmoDUInfo.isExcalibur4G5GTDD || changeforTDD2cAdd || changeforTDD1c2cNSBAdd 					// [12082021] GMO_TMO-206
						|| changeforTDDMMBB) {									// [02092022] GMO_TMO-237
						String nrCellRelationId2 = nrCellRelationId;
						StringBuilder nrCellRelationsb2 = new StringBuilder(nrCellRelationId2);
						nrCellRelationsb2.insert(3, "nci_");
						nrCellRelationsb2 = !changeforTDD2cAdd && !changeforTDD1c2cNSBAdd && !changeforTDDMMBB ? nrCellRelationsb2.append("1") : nrCellRelationsb2;	// [12142021] GMO_TMO-206, [02092022] GMO_TMO-237
						sb.append("crn GNBCUCPFunction=1,NRCellCU=$" + currNRCellDUId + ",NRCellRelation=$" + nrCellRelationsb2 + eol);
					}else {
						sb.append("crn GNBCUCPFunction=1,NRCellCU=$" + currNRCellDUId + ",NRCellRelation=$" + nrCellRelationId + eol);
					}
					sb.append("cellIndividualOffsetNR 0" + eol);
					sb.append("coverageIndicator 0" + eol);
					sb.append("includeInSIB true" + eol);
					sb.append("isHoAllowed true" + eol);
					sb.append("nRCellRef NRCellCU=$" + nrCellRelationId + eol);
					sb.append("nRFreqRelationRef NRCellCU=$" + currNRCellDUId + ",NRFreqRelation=$ssbarfcn" + eol);
					//[05122021 - ezrxxsu] ribtmEnabled is deprecated for SW >= 21.Q1
					if(!CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "21.Q1")) {
						sb.append("ribtmEnabled false" + eol);
					}
					sb.append("sCellCandidate 0" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
				NRCellRelationIdList.clear();
			}

			// check for nr 2nd carrier presence
			if (duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
				Map<String, NRCellObj> nrCellMap = new TreeMap<String, NRCellObj>(duInfo.getNrSiteObj().getnRCellMap());
				for (Entry<String, NRCellObj> kvp : nrCellMap.entrySet()) {
					String currCellFddName = kvp.getKey();
					if (currCellFddName.startsWith("A") && currCellFddName.endsWith("2")) {
						nrTwoCarrier = true;
						break;
					}
				}
			}

			// nr 2nd carrier for TDD
			if((nrTwoCarrier && duInfo.tmoDUInfo.isExcalibur4G5GTDD) || changeforTDD2cAdd || changeforTDD1c2cNSBAdd     // [12092021] GMO_TMO-206
				|| changeforTDDMMBB) {							// [02092022] GMO_TMO-237
				sb.append("WAIT 5" + eol);
				sb.append(genericScriptBlockGenerator.generateSingleLineComment("N41 2C NRCA 3sec"));
				sb.append("func N41_2C_NRCA_3sec" + eol);
				sb.append("$ssbarfcn2c = $1" + eol + eol);

				Map<String, NRCellObj> nrCellMap = new TreeMap<String, NRCellObj>(duInfo.getNrSiteObj().getnRCellMap());
				/* {
					for(Entry<String, NRCellObj> kvp : nrCellMap.entrySet()) {
						String currCellFddName = kvp.getKey();
						String cellNumber = currCellFddName.substring(currCellFddName.length() - 2);
						String nrCellDUId = "id_NRCellDU" + cellNumber;

						if(!NRCellDUIdList.contains(nrCellDUId)) {
							NRCellDUIdList.add(nrCellDUId);
						}

						String lastSecondDigit = currCellFddName.substring(currCellFddName.length() - 2, currCellFddName.length() - 1);
						String lastDigit = currCellFddName.substring(currCellFddName.length() - 1, currCellFddName.length());   // [12082021] GMO_TMO-206
						if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd//) {      	// [12082021] GMO_TMO-206
							|| (changeforTDDMMBB)) {								// [02092022] GMO_TMO-237
							nrCellDUId = "id_NRCellDU" + lastSecondDigit + lastDigit;
							if (!lastDigit.contentEquals("2")) {   // Do not continue if not 2nd carrier cell
								continue;
							}
						}
						sb.append("get GNBDUFunction=1,NRCellDU=.*" + cellNumber + "$ NRCellDUId > $" + nrCellDUId + eol);
					}
					sb.append(eol);
					
					for(Entry<String, NRCellObj> kvp : nrCellMap.entrySet()) {
						String currCellFddName = kvp.getKey();
						String cellNumber = currCellFddName.substring(currCellFddName.length()-2);
						if(currCellFddName.startsWith("A") && currCellFddName.endsWith("2")) {
							sb.append("get GNBDUFunction=1,NRCellDU=.*" + cellNumber + "$ nCI > $id_nci_NRCellDU" + cellNumber + eol);
							sb.append("$id_nci_NRCellDU" + cellNumber + " = auto$id_nci_NRCellDU" + cellNumber + eol);
						}
					}					
				}*/
				{					// [02102022] GMO_TMO-237, generate for all cases with N41, even if only 1C
					ArrayList<String> trackCellNumberList = new ArrayList<String>();
					for(Entry<String, NRCellObj> kvp : nrCellMap.entrySet()) {
						String currCellFddName = kvp.getKey();
						String cellNumber = currCellFddName.substring(currCellFddName.length()-2, currCellFddName.length()-1);	// Get only sector number
						cellNumber = cellNumber + "2";			// 2 for 2nd char equivalent name
						String nrCellDUId = "id_NRCellDU" + cellNumber;

						if(!NRCellDUIdList.contains(nrCellDUId)) {
							NRCellDUIdList.add(nrCellDUId);
						}

						if (!trackCellNumberList.contains(nrCellDUId))	{
							sb.append("get GNBDUFunction=1,NRCellDU=.*" + cellNumber + "$ NRCellDUId > $" + nrCellDUId + eol);

							trackCellNumberList.add(nrCellDUId);
						}
					}
					sb.append(eol);
					
					for(Entry<String, NRCellObj> kvp : nrCellMap.entrySet()) {
						String currCellFddName = kvp.getKey();
						if(currCellFddName.startsWith("A")) {
							String cellNumber = currCellFddName.substring(currCellFddName.length()-2, currCellFddName.length()-1);	// Get only sector number
							cellNumber = cellNumber + "2";			// 2 for 2nd char equivalent name
							
							if (!trackCellNumberList.contains(cellNumber))	{
								sb.append("get GNBDUFunction=1,NRCellDU=.*" + cellNumber + "$ nCI > $id_nci_NRCellDU" + cellNumber + eol);
								sb.append("$id_nci_NRCellDU" + cellNumber + " = auto$id_nci_NRCellDU" + cellNumber + eol);
								
								trackCellNumberList.add(cellNumber);
							}
						}
					}					
				}
				sb.append(eol);
				sb.append("$NRFreqid2c = $ssbarfcn2c-30-20-0-1" + eol + eol);
				sb.append("pr GNBCUCPFunction=1,NRNetwork=1,NRFrequency=$NRFreqid2c" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1,NRNetwork=1,NRFrequency=$NRFreqid2c" + eol);
				sb.append("arfcnValueNRDl $ssbarfcn2c" + eol);
				sb.append("smtcDuration 1" + eol);
				sb.append("smtcOffset 0" + eol);
				sb.append("smtcPeriodicity 20" + eol);
				sb.append("smtcScs 30" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol + eol);

				Collections.sort(NRCellDUIdList);

				for(Entry<String, NRCellObj> nrCellObject : nrCellMap.entrySet()) {
					String nrCell = nrCellObject.getKey();
					if(nrCell.endsWith("2")) continue;
					String cellNumber = nrCell.substring(nrCell.length()-2);
					String NRCellCU = "id_NRCellDU" + cellNumber;

					sb.append("pr GNBCUCPFunction=1,NRCellCU=$" + NRCellCU + ",NRFreqRelation=$ssbarfcn2c" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,NRCellCU=$" + NRCellCU + ",NRFreqRelation=$ssbarfcn2c" + eol);
					String cellReselectionPriority = "7";
					if(!duInfo.tmoDUInfo.hasExcalibur4G5G) {
						String sourceBand = duInfo.nodeBandType.toUpperCase();
						String targetBand = duInfo.nodeBandType.toUpperCase();
						cellReselectionPriority = TMO_CommonUtil.calculateMarketSpecficCellReselectionPriorityValue(duInfo, sourceBand, targetBand, cellReselectionPriority);
					}
					sb.append("cellReselectionPriority " + cellReselectionPriority + eol);
					sb.append("nRFrequencyRef NRNetwork=1,NRFrequency=$NRFreqid2c" + eol);
					sb.append("pMax 23" + eol);
					sb.append("qOffsetFreq 0" + eol);
					sb.append("qQualMin " + eol);
					sb.append("qRxLevMin -140" + eol);
					sb.append("sIntraSearchP 62" + eol);
					sb.append("sIntraSearchQ " + eol);
					sb.append("tReselectionNR 2" + eol);
					sb.append("threshXHighP 4" + eol);
					sb.append("threshXHighQ " + eol);
					sb.append("threshXLowP 0" + eol);
					sb.append("threshXLowQ " + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}

				String isHoAllowed = "false";			// [01112022] Default for most scopes

				//NR CellRelation
				for(Entry<String, NRCellObj> nrCellObject : nrCellMap.entrySet()) {
					String nrCell = nrCellObject.getKey();
					if(nrCell.endsWith("2")) continue;
					// A11. A21, A31
					String sectorNo = nrCell.substring(nrCell.length()-2, nrCell.length()-1);
					String Carrier = nrCell.substring(nrCell.length()-1);
					String NRCellCU = "id_NRCellDU" + sectorNo + Carrier;
					String NRCellCUNCI = "id_nci_NRCellDU" + sectorNo + "2";
					String NRCellCU1 = "id_NRCellDU" + sectorNo + "2";

					if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd				// [12092021] GMO_TMO-206
						|| changeforTDDMMBB) {									// [02092022] GMO_TMO-237
						sb.append("pr GNBCUCPFunction=1,NRCellCU=$" + NRCellCU + ",NRCellRelation=$" + NRCellCU1 + eol);
						sb.append("$id = $nr_of_mos" + eol);
					}
					sb.append("pr GNBCUCPFunction=1,NRCellCU=$" + NRCellCU + ",NRCellRelation=$" + NRCellCUNCI + eol);

					/* Per Rubal, December 10, 2021:
					 * coverageIndicator 2 and sCellCandidate 1 needs to be set when creating relation from N41 1C towards N41 2C (sector by sector i.e alpha to alpha/beta to beta and so on)
					 * coverageIndicator 0 and sCellCandidate 0 needs to be set for relations from N41 1C towards N41 1C.
					 * No relations needs to be there in script from N41 2C towards any other band (same reflected in sample provided so we are good here).*/
					String coverageIndicator = "0";
					String sCellCandidate = "0";
					if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd		  		// [12092021] GMO_TMO-206
						|| changeforTDDMMBB) {									// [02092022] GMO_TMO-237
						sb.append("$id1 = $nr_of_mos" + eol);
						sb.append("if $id = 0 && $id1 = 0" + eol);
						coverageIndicator = "2";
						sCellCandidate = "1";
						//isHoAllowed = "true";	// [01112022]
						isHoAllowed = "false"; //[ezrxxsu - 03072022] GMO_TMO-267
					}
					else {
						sb.append("if $nr_of_mos = 0" + eol);
						if(changeforTDDMMBB) {  //Excalibur_207
							coverageIndicator = "2";
							sCellCandidate = "1";
						}
					}

					sb.append("crn GNBCUCPFunction=1,NRCellCU=$" + NRCellCU + ",NRCellRelation=$" + NRCellCUNCI + eol);
					sb.append("cellIndividualOffsetNR 0" + eol);
					sb.append("coverageIndicator " + coverageIndicator + eol);
					sb.append("includeInSIB true" + eol);
					sb.append("isHoAllowed " + isHoAllowed + eol);
					sb.append("nRCellRef NRCellCU=$" + NRCellCU1 + eol);
					sb.append("nRFreqRelationRef NRCellCU=$" + NRCellCU + ",NRFreqRelation=$ssbarfcn2c" + eol);
					sb.append("sCellCandidate " + sCellCandidate + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
				sb.append("WAIT 5" + eol);
				sb.append(eol);
				if(!duInfo.tmoDUInfo.isExcalibur4G5GTDD
						&& !(nrTwoCarrier || changeforN41 || changeforTDDMMBB || changeforTDD2cAdd || changeforTDD1c2cNSBAdd)) {					// [02082022] GMO_TMO-237, Remove only for n41 in general, irrespective of carriers

					sb.append(genericScriptBlockGenerator.generateComment("Activating NR CA Features"));
					sb.append("set Lm=1,FeatureState=CXC4012477 featurestate 1" + eol);
					sb.append("set Lm=1,FeatureState=CXC4012478 featurestate 1" + eol);
					sb.append(genericScriptBlockGenerator.generateComment("NR CA system constants"));
					// [12172021] GMO_TMO-206. Added for all scopes. will only enable of NR CA add (sCellCandidate 1)
					sb.append("# Enable NR CA if NRCellRelation sCellCandidate is enabled" + eol);
					sb.append("get NRCellRelation=.* sCellCandidate 1" + eol);
					sb.append("if $nr_of_mos > 0" + eol);

					sb.append("scw RP505:1" + eol);
					sb.append("fi" + eol);		// [12172021] GMO_TMO-20
				}
				
				if (!changeforTDD2cAdd && !changeforTDD1c2cNSBAdd			// [12172021] GMO_TMO-206. Keep only RP505:1 system constant and remove RP893.
					&& !changeforTDDMMBB)	 {								// [02102022] GMO_TMO-237
					sb.append("scw RP893:1" + eol);
				}
				sb.append(eol);
				sb.append("endfunc" + eol);
				sb.append(eol);

		        sb.append(genericScriptBlockGenerator.generateSingleLineComment("N41 1C 4sec"));
				sb.append("func N41_1C_4sec" + eol);
				sb.append(eol);
				if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd				// [12102021] GMO_TMO-206  maybe can be applied for all scopes?
					|| changeforTDDMMBB)	{								// [02092022] GMO_TMO-237
					sb.append("get GNBDUFunction=1,NRCellDU=.*1$ ssbFrequencyAutoSelected > $ssbarfcn" + eol);
					sb.append("get GNBDUFunction=1,NRCellDU=.*41$ NRCellDUId > $id_NRCellDU41" + eol);
				}
				else {
					sb.append("get GNBDUFunction=1,NRCellDU=.*11$ ssbFrequencyAutoSelected > $ssbarfcn" + eol);
					sb.append("get GNBDUFunction=1,NRCellDU=.*41$ NRCellDUId > $id_NRCellDU4" + eol);
				}
				sb.append(eol);
				sb.append("get GNBDUFunction=1,NRCellDU=.*41$ nCI > $id_nci_NRCellDU41" + eol);
				sb.append("$id_nci_NRCellDU41 = auto$id_nci_NRCellDU41" + eol);
				sb.append(eol);
				sb.append("$NRFreqid = $ssbarfcn-30-20-0-1" + eol);
				sb.append(eol);
				if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd				// [12102021] GMO_TMO-206  maybe can be applied for all scopes?
					|| changeforTDDMMBB) {									// [02092022] GMO_TMO-237
					sb.append("pr GNBCUCPFunction=1,NRCellCU=$id_NRCellDU41,NRFreqRelation=$ssbarfcn" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,NRCellCU=$id_NRCellDU41,NRFreqRelation=$ssbarfcn" + eol);
				}
				else {
					sb.append("pr GNBCUCPFunction=1,NRCellCU=$id_NRCellDU4,NRFreqRelation=$ssbarfcn" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
					sb.append("crn GNBCUCPFunction=1,NRCellCU=$id_NRCellDU4,NRFreqRelation=$ssbarfcn" + eol);
				}
				String cellReselectionPriority = "7";
				if(!duInfo.tmoDUInfo.hasExcalibur4G5G) {
					String sourceBand = duInfo.nodeBandType.toUpperCase();
					String targetBand = duInfo.nodeBandType.toUpperCase();
					cellReselectionPriority = TMO_CommonUtil.calculateMarketSpecficCellReselectionPriorityValue(duInfo, sourceBand, targetBand, cellReselectionPriority);
				}
				sb.append("cellReselectionPriority "+ cellReselectionPriority + eol);
				sb.append("nRFrequencyRef NRNetwork=1,NRFrequency=$NRFreqid" + eol);
				sb.append("pMax 23" + eol);
				sb.append("qOffsetFreq 0" + eol);
				sb.append("qQualMin " + eol);
				sb.append("qRxLevMin -140" + eol);
				sb.append("sIntraSearchP 62" + eol);
				sb.append("sIntraSearchQ " + eol);
				sb.append("tReselectionNR 2" + eol);
				sb.append("threshXHighP 4" + eol);
				sb.append("threshXHighQ " + eol);
				sb.append("threshXLowP 0" + eol);
				sb.append("threshXLowQ " + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				for(Entry<String, NRCellObj> nrCellObject : nrCellMap.entrySet()) {
					String nrCell = nrCellObject.getKey();
					String sectorNo = nrCell.substring(nrCell.length()-2, nrCell.length()-1);
					String Carrier = nrCell.substring(nrCell.length()-1);
					String NRCellCU = "$id_NRCellDU" + sectorNo;
					String NRCellCUNCI = "$id_nci_NRCellDU" + sectorNo + "1";
					if(sectorNo.equals("4")) continue;
					if(Carrier.equals("2")) continue;
					if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd				// [12102021] GMO_TMO-206  maybe can be applied for all scopes?
						|| changeforTDDMMBB) {									// [02092022] GMO_TMO-237
						NRCellCU = NRCellCU + "1";
						sb.append("pr GNBCUCPFunction=1,NRCellCU=$id_NRCellDU41,NRCellRelation=" + NRCellCU + eol);
						sb.append("$id = $nr_of_mos" + eol);
						sb.append("pr GNBCUCPFunction=1,NRCellCU=$id_NRCellDU41,NRCellRelation=" + NRCellCUNCI + eol);
						sb.append("$id1 = $nr_of_mos" + eol);
						sb.append("if $id = 0 && $id1 = 0" + eol);        
						sb.append("crn GNBCUCPFunction=1,NRCellCU=$id_NRCellDU41,NRCellRelation=" + NRCellCUNCI + eol);
					}
					else {
						sb.append("pr GNBCUCPFunction=1,NRCellCU=$id_NRCellDU4,NRCellRelation=" + NRCellCUNCI + eol);
						sb.append("if $nr_of_mos = 0" + eol);
						sb.append("crn GNBCUCPFunction=1,NRCellCU=$id_NRCellDU4,NRCellRelation=" + NRCellCUNCI + eol);
					}
					sb.append("cellIndividualOffsetNR 0" + eol);
					sb.append("coverageIndicator 0" + eol);
					sb.append("includeInSIB true" + eol);
					sb.append("isHoAllowed true" + eol);
					sb.append("nRCellRef NRCellCU=" + NRCellCU + eol);
					if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd				// [12102021] GMO_TMO-206  maybe can be applied for all scopes?
						|| changeforTDDMMBB) {									// [02092022] GMO_TMO-237
						sb.append("nRFreqRelationRef NRCellCU=$id_NRCellDU41,NRFreqRelation=$ssbarfcn" + eol);
					}
					else {
						sb.append("nRFreqRelationRef NRCellCU=$id_NRCellDU4,NRFreqRelation=$ssbarfcn" + eol);
					}
					sb.append("sCellCandidate 0" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
				for(Entry<String, NRCellObj> nrCellObject : nrCellMap.entrySet()) {
					String nrCell = nrCellObject.getKey();
					String Carrier = nrCell.substring(nrCell.length()-1);
					String sectorNo = nrCell.substring(nrCell.length()-2, nrCell.length()-1);
					String NRCellCU = "$id_NRCellDU" + sectorNo;
					if(sectorNo.equals("4"))continue;
					if(Carrier.equals("2"))continue;
					if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd		  		// [12092021] GMO_TMO-206
						|| changeforTDDMMBB)	{								// [02092022] GMO_TMO-237
						NRCellCU = NRCellCU + "1";
						sb.append("pr GNBCUCPFunction=1,NRCellCU=" + NRCellCU + ",NRCellRelation=$id_NRCellDU41" + eol);
						sb.append("$id = $nr_of_mos" + eol);
						sb.append("pr GNBCUCPFunction=1,NRCellCU=" + NRCellCU + ",NRCellRelation=$id_nci_NRCellDU41" + eol);
						sb.append("$id1 = $nr_of_mos" + eol);
						sb.append("if $id = 0 && $id1 = 0" + eol);        
					}
					else {
						sb.append("pr GNBCUCPFunction=1,NRCellCU=" + NRCellCU + ",NRCellRelation=$id_nci_NRCellDU41" + eol);
						sb.append("if $nr_of_mos = 0" + eol);
			        }
					sb.append("crn GNBCUCPFunction=1,NRCellCU=" + NRCellCU + ",NRCellRelation=$id_nci_NRCellDU41" + eol);
					sb.append("cellIndividualOffsetNR 0" + eol);
					sb.append("coverageIndicator 0" + eol);
					sb.append("includeInSIB true" + eol);
					sb.append("isHoAllowed true" + eol);
					sb.append("nRCellRef NRCellCU=$id_NRCellDU41" + eol);
					sb.append("nRFreqRelationRef NRCellCU=" + NRCellCU + ",NRFreqRelation=$ssbarfcn" + eol);
					sb.append("sCellCandidate 0" + eol);
					sb.append("end" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
				}
				sb.append("endfunc" + eol);
				sb.append(eol);
				sb.append("$4SEC = 0" + eol);
				sb.append("pr GNBDUFunction=1,NRCellDU=.*41$" + eol);
				sb.append("if $nr_of_mos != 0" + eol);
				sb.append("$4SEC = 1" + eol);
				sb.append("N41_1C_4sec" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
		        sb.append(genericScriptBlockGenerator.generateSingleLineComment("N41 2C NRCA 4sec"));
				sb.append("func N41_2C_NRCA_4sec" + eol);
				sb.append(eol);
				sb.append("$ssbarfcn2c = $1" + eol);
				sb.append(eol);
				sb.append("get GNBDUFunction=1,NRCellDU=.*41$ NRCellDUId > $id_NRCellDU41" + eol);
				sb.append("get GNBDUFunction=1,NRCellDU=.*42$ NRCellDUId > $id_NRCellDU42" + eol);
				sb.append(eol);
				sb.append("get GNBDUFunction=1,NRCellDU=.*42$ nCI > $id_nci_NRCellDU42" + eol);
				sb.append("$id_nci_NRCellDU42 = auto$id_nci_NRCellDU42" + eol);
				sb.append(eol);
				sb.append("$NRFreqid2c = $ssbarfcn2c-30-20-0-1" + eol);
				sb.append(eol);
				sb.append("pr GNBCUCPFunction=1,NRCellCU=$id_NRCellDU41,NRFreqRelation=$ssbarfcn2c" + eol);
				sb.append("if $nr_of_mos = 0" + eol);
				sb.append("crn GNBCUCPFunction=1,NRCellCU=$id_NRCellDU41,NRFreqRelation=$ssbarfcn2c" + eol);
				cellReselectionPriority = "7";
				if(!duInfo.tmoDUInfo.hasExcalibur4G5G) {
					String sourceBand = duInfo.nodeBandType.toUpperCase();
					String targetBand = duInfo.nodeBandType.toUpperCase();
					cellReselectionPriority = TMO_CommonUtil.calculateMarketSpecficCellReselectionPriorityValue(duInfo, sourceBand, targetBand, cellReselectionPriority);
				}
				sb.append("cellReselectionPriority "+ cellReselectionPriority + eol);
				sb.append("nRFrequencyRef NRNetwork=1,NRFrequency=$NRFreqid2c" + eol);
				sb.append("pMax 23" + eol);
				sb.append("qOffsetFreq 0" + eol);
				sb.append("qQualMin " + eol);
				sb.append("qRxLevMin -140" + eol);
				sb.append("sIntraSearchP 62" + eol);
				sb.append("sIntraSearchQ " + eol);
				sb.append("tReselectionNR 2" + eol);
				sb.append("threshXHighP 4" + eol);
				sb.append("threshXHighQ " + eol);
				sb.append("threshXLowP 0" + eol);
				sb.append("threshXLowQ " + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd		  		// [12092021] GMO_TMO-206
					|| changeforTDDMMBB)	{								// [02092022] GMO_TMO-237
					sb.append("pr GNBCUCPFunction=1,NRCellCU=$id_NRCellDU41,NRCellRelation=$id_NRCellDU42" + eol);
					sb.append("$id = $nr_of_mos" + eol);
					sb.append("pr GNBCUCPFunction=1,NRCellCU=$id_NRCellDU41,NRCellRelation=$id_nci_NRCellDU42" + eol);
					sb.append("$id1 = $nr_of_mos" + eol);
					sb.append("if $id = 0 && $id1 = 0" + eol);        

					//isHoAllowed = "true";	// [01112022]
					isHoAllowed = "false"; //[ezrxxsu - 03072022] GMO_TMO-267
				}
				else {
					sb.append("pr GNBCUCPFunction=1,NRCellCU=$id_NRCellDU41,NRCellRelation=$id_nci_NRCellDU42" + eol);
					sb.append("if $nr_of_mos = 0" + eol);
				}
				sb.append("crn GNBCUCPFunction=1,NRCellCU=$id_NRCellDU41,NRCellRelation=$id_nci_NRCellDU42" + eol);
				sb.append("cellIndividualOffsetNR 0" + eol);
				sb.append("coverageIndicator 2" + eol);
				sb.append("includeInSIB true" + eol);
				sb.append("isHoAllowed " + isHoAllowed + eol);
				sb.append("nRCellRef NRCellCU=$id_NRCellDU42" + eol);
				sb.append("nRFreqRelationRef NRCellCU=$id_NRCellDU41,NRFreqRelation=$ssbarfcn2c" + eol);
				sb.append("sCellCandidate 1" + eol);
				sb.append("end" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("endfunc" + eol);
				sb.append(eol);
				sb.append("###############################################################################################################" + eol);
				sb.append(eol);
				sb.append("pr GNBDUFunction=1,NRCellDU=.*2$" + eol);
				sb.append("if $nr_of_mos != 0" + eol);
				if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd			 	// [12102021] GMO_TMO-206 maybe can be applied for all scopes?
					|| changeforTDDMMBB)	{								// [02092022] GMO_TMO-237
					sb.append("get GNBDUFunction=1,NRCellDU=.*2$ ssbFrequencyAutoSelected > $ssbarfcn2c" + eol);
				}
				else {
					sb.append("get GNBDUFunction=1,NRCellDU=.*12$ ssbFrequencyAutoSelected > $ssbarfcn2c" + eol);
				}
				sb.append("N41_2C_NRCA_3sec $ssbarfcn2c" + eol);
				sb.append("fi" + eol);
				sb.append(eol);
				sb.append("pr GNBDUFunction=1,NRCellDU=.*2$" + eol);
				sb.append("if $nr_of_mos != 0 && $4SEC = 1" + eol);
				if (changeforTDD2cAdd || changeforTDD1c2cNSBAdd		 		 // [12102021] GMO_TMO-206 maybe can be applied for all scopes?
					|| changeforTDDMMBB)	{								// [02092022] GMO_TMO-237
					sb.append("get GNBDUFunction=1,NRCellDU=.*2$ ssbFrequencyAutoSelected > $ssbarfcn2c" + eol);
				}
				else {
					sb.append("get GNBDUFunction=1,NRCellDU=.*12$ ssbFrequencyAutoSelected > $ssbarfcn2c" + eol);
				}
				sb.append("N41_2C_NRCA_4sec $ssbarfcn2c" + eol);
				sb.append("fi" + eol);
				sb.append(eol);

				List<HashMap<String, String>> nr_Carrier_AggregationList = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_NR Carrier Aggregation"), "NRCellRelation", ".+");
				if(nr_Carrier_AggregationList != null && !nr_Carrier_AggregationList.isEmpty()) {
					for (HashMap<String, String> nr_Carrier_Aggregation : nr_Carrier_AggregationList) {
						String nrCellRelation = nr_Carrier_Aggregation.get("NRCellRelation");
						String nrGutranCell = nr_Carrier_Aggregation.get("NRCellCU");
						String nrScellCandidate = nr_Carrier_Aggregation.get("sCellCandidate");
						String nrCoverageIndicator = nr_Carrier_Aggregation.get("coverageIndicator");

						String gUtranCellNCI = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GUTRANCELLINFO"), "nCI", nrCellRelation, "gUtranCell");
						if(gUtranCellNCI.startsWith("A") && gUtranCellNCI.endsWith("2")) {
							sb.append(eol);
//               	        sb.append("### setting from nr carrier aggregation tab " + eol);	
							sb.append("set GNBCUCPFunction=1,NRCellCU=" + nrGutranCell + ",NRCellRelation=auto" + nrCellRelation + "$ coverageIndicator " + nrCoverageIndicator + eol);
							sb.append("set GNBCUCPFunction=1,NRCellCU=" + nrGutranCell + ",NRCellRelation=auto" + nrCellRelation + "$ sCellCandidate " + nrScellCandidate + eol);
						}
					}
					sb.append(eol);
				}
				else {						// [02082022] GMO_TMO-237 Added comment, hardcoded values for n41 node with 1C+2C, not applicable if only 1C
					HashMap<String, String> nCell2cNci = new HashMap<String, String>();			// Need to find N41 2C NCI for creating relations from 1C

					for (Entry<String, SiteCellObj> cellInfoEntry : duInfo.newCellToCellInfo.entrySet()) {
						String nrGutranCell = cellInfoEntry.getKey();

						if(nrGutranCell.startsWith("A") && nrGutranCell.endsWith("2")) {
							if (!cellInfoEntry.getValue().nCI.isEmpty()) {
								nCell2cNci.put(nrGutranCell, cellInfoEntry.getValue().nCI);
							}
						}
					}

					if (!nCell2cNci.isEmpty()) {
						sb.append(genericScriptBlockGenerator.generateComment("Scellcandidates/coverageindicator -- replace NCI value for N41 2C cells in below commands."));

						String nrScellCandidate = "1";				// hard-code for now per ticket
						String nrCoverageIndicator = "2";			// hard-code for now per ticket

						for (Entry<String, SiteCellObj> cellInfoEntry : duInfo.newCellToCellInfo.entrySet()) {
							String nrGutranCell = cellInfoEntry.getKey();

							if(nrGutranCell.startsWith("A") && nrGutranCell.endsWith("1")) {
								String nrGutranCell2c = nrGutranCell.substring(0, nrGutranCell.length()-1) + "2";	// Need to 2C, corresponding to 1C sector, cell in NCI Map
								String nrCellRelation = nCell2cNci.get(nrGutranCell2c);
								
								if (!nrCellRelation.isEmpty()) {
									sb.append(eol);
									sb.append("set GNBCUCPFunction=1,NRCellCU=" + nrGutranCell + ",NRCellRelation=auto" + nrCellRelation + "$ coverageIndicator " + nrCoverageIndicator + eol);
									sb.append("set GNBCUCPFunction=1,NRCellCU=" + nrGutranCell + ",NRCellRelation=auto" + nrCellRelation + "$ sCellCandidate " + nrScellCandidate + eol);
								}
							}
						}
						sb.append(eol);
					}
				}
				
	
				boolean isN411c2cPresent = false;
				String gUtranCell = "";
				String gnbidnca = "";
				String gnbnamenca = "";
				boolean isTandTFound = false;
				if(duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
					gUtranCellMapList = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GUTRANCELLINFO"), "gUtranCell", ".+");
					for(HashMap<String, String> gUtranCellMap : gUtranCellMapList ) {
						gUtranCell = gUtranCellMap.get("gUtranCell");
						gnbidnca = gUtranCellMap.get("gNBID");
						gnbnamenca = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GNBINFO"), "gNBID", gnbidnca, "gNB Name");
						if(gUtranCell.startsWith("A") && gUtranCell.endsWith("1") && gnbnamenca.startsWith("M") && gnbnamenca.endsWith("3")) {
							for(HashMap<String, String> gUtranCellMap2 : gUtranCellMapList ) {
								String	gUtranCell2 = gUtranCellMap2.get("gUtranCell");
								String	gnbidnca2 = gUtranCellMap.get("gNBID");
								String	gnbnamenca2 = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GNBINFO"), "gNBID", gnbidnca2, "gNB Name");
								if(gUtranCell2.startsWith("A") && gUtranCell2.endsWith("2") && gnbnamenca2.startsWith("M") && gnbnamenca2.endsWith("3")) {
									isN411c2cPresent = true;
									break;
								}
							}
							break;
						}
					}
				}

				if(isN411c2cPresent && duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
					for (HashMap<String, String> nr_Carrier_Aggregation : nr_Carrier_AggregationList) {
						String gUtrancellnca = nr_Carrier_Aggregation.get("NRCellCU");
						String nrCellRelationnca = nr_Carrier_Aggregation.get("NRCellRelation");
						String nrScellCandidatenca = nr_Carrier_Aggregation.get("sCellCandidate");
						gnbidnca = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GUTRANCELLINFO"), "gUtranCell", gUtrancellnca, "gNBID");
						gnbnamenca = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GNBINFO"), "gNBID", gnbidnca, "gNB Name");
						String ncigUtranCell = CSVUtils.readDataFromCSVFile(CSVUtils.getCIQCSVFile("RNDCIQ_GUTRANCELLINFO"), "nCI", nrCellRelationnca, "gUtranCell");
						if(duInfo.tmoDUInfo.isExcalibur4G5GTDD) {
							if(isN411c2cPresent) {
								if(duInfo.duName.equals(gnbnamenca) && gUtrancellnca.startsWith("A")) {
									if(gnbnamenca.startsWith("M") && gnbnamenca.endsWith("3")) {
										if(ncigUtranCell.startsWith("A") && ncigUtranCell.endsWith("2")) {
											if(nrScellCandidatenca.equals("1")) {
												isTandTFound = true;
												break;
											}
										}
									}
								}
							}
						}
					}
				}
				if(isTandTFound) {
					sb.append(genericScriptBlockGenerator.generateComment("Enable NR CA if T+T Found in CIQ"));
					sb.append("pr NRCellDU=" + eol);
					sb.append("if $nr_of_mos != 0" + eol);
					sb.append("deb NRCellDU=" + eol);
					sb.append("fi" + eol);
					sb.append(eol);
					sb.append("mr celldugrp" + eol);
					sb.append(eol);
					sb.append("ma celldugrp ,NRCellDU=.*1$ administrativeState 1" + eol);
					sb.append("bl celldugrp" + eol);
					sb.append("wait 10" + eol);
					sb.append(eol);
					sb.append("set Lm=1,FeatureState=CXC4012477 featurestate 1 " + eol);
					sb.append("set Lm=1,FeatureState=CXC4012478 featurestate 1 " + eol);
					sb.append("set NRCellDU=.*1$ additionalPucchForCaEnabled true" + eol);
					sb.append(eol);
					sb.append(eol);
					sb.append("mr celldugrp" + eol);
				}
			}		
			//[12172020] Include below block for MMBB Var2/Var3
			if((!changeForMmbb || changeforTDD2cAdd || changeforTDD1c2cNSBAdd
					|| changeforTDDMMBB)			 				// [02092022] GMO_TMO-237
					&& (duInfo.isNR600 || duInfo.tmoDUInfo.isMidBandAnchorScope || duInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio || changeForMMBBNSB || changeforTDDMMBB || duInfo.tmoDUInfo.isExcalibur4G5GFDD || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope()) || changeforTDD2cAdd || changeforTDD1c2cNSBAdd)) {
				sb.append("WAIT 5" + eol);
		        sb.append(genericScriptBlockGenerator.generateSingleLineComment("transmitsib2,4 set only when NRfreqrelation for 1c cells only"));
				sb.append("set NRCellCU=.*1$ transmitSib2 true" + eol);
				sb.append("set NRCellCU=.*1$ transmitSib4 true" + eol);
				sb.append(eol);
				sb.append("pr GNBCUCPFunction=1,NRCellCU.*,EUtranFreqRelation" + eol);
				sb.append("if $nr_of_mos != 0" + eol);
				sb.append("set NRCellCU=.*1$ transmitSib5 true" + eol);
				sb.append("fi" + eol);
				
				//[ezrxxsu - 03152022] - GMO_TMO-275
				if(!duInfo.tmoDUInfo.hasExcalibur4G5G && duInfo.subNetwork.contentEquals("Charlotte")) {
					if(duInfo.tmoDUInfo.isMidBandTddMMBBVariation || duInfo.nodeBandType.contentEquals("N41")) {
						sb.append(eol);
						sb.append("func Charlotte_SIB" + eol);
						sb.append("set NRCellCU=.*1$ transmitSib2 false" + eol);
						sb.append("set NRCellCU=.*1$ transmitSib4 false" + eol);
						sb.append(eol);
						sb.append("pr GNBCUCPFunction=1,NRCellCU.*,EUtranFreqRelation" + eol);
						sb.append("if $nr_of_mos != 0" + eol);
						sb.append("set NRCellCU=.*1$ transmitSib5 false" + eol);
						sb.append("fi" + eol + eol);
						sb.append("endfunc" + eol + eol);
						sb.append("if $mibprefix ~ Charlotte" + eol);
						sb.append("Charlotte_SIB" + eol);
						sb.append("fi" + eol + eol);
					}
				}
			}

			String comment = "";		// [02212022] GMO_TMO-257
			if (!duInfo.tmoDUInfo.isExcalibur4G5GTDD && !duInfo.tmoDUInfo.isExcalibur4G5GFDD && (changeforTDDMMBB || changeforTDD2cAdd || changeforTDD1c2cNSBAdd)) {		// [02102022] GMO_TMO-237 n41 in general
				generateEnableNrCa(sb, "IntraFreqInterGnb", comment);
			}

			sb.append(eol);
			sb.append("deb unlockedcell" + eol);
			sb.append("mr unlockedcell" + eol);
			sb.append(eol);
			sb.append("unset all" + eol);
			sb.append(eol);
			
			if ((!changeForMmbb && !changeForMMBBNSB) || changeforTDDMMBB || changeforTDD2cAdd || changeforTDD1c2cNSBAdd) {
				sb.append("$date = `date +%y%m%d-%H%M`" + eol);
				sb.append("cvmk CV_post_NRIntra_relation_$date" + eol + eol);
			}

			sb.append("gs-" + eol);
			sb.append("Confbdl-" + eol);

			FileUtil.writeToFile(sb, file);
		}
		catch (Exception e) {
			Logger.logger.error("generateIntraFreqInterGnbRelationScript exception!", e);
			Logger.getGmoLogger().printError("Error generating IntraFreq InterGnb Relation Script! " + e.getMessage());
		}
	}
	
	/**
	 * Function to generate PTP Slave Configuration Script
	 * @param duInfo
	 * @param file
	 * @param eolType
	 */
	private void generatePTPSlaveConfigurationScript(SiteCellObj duInfo, String file, String eolType) 
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();
		
		try 
		{	
			String tnPort = "";
			if(duInfo.tmoDUInfo.getIsMidBandAnchorScopeWith6449Radio() || (duInfo.tmoDUInfo.getIsStandaloneN41Node() && !duInfo.tmoDUInfo.getIsMidbandMixedModeBasebandScope())) {
				tnPort = "TN_IDL_B";
			}else {
				tnPort = "TN_A";
			}
			sb.append("Confbdl+" + eol);
			sb.append("gs+" + eol);
			sb.append(eol);
			sb.append("lt all" + eol);
			sb.append(eol);
			
			sb.append("$date = `date +%y%m%d-%H%M`" + eol);
			sb.append("cvms Pre_PTP_Configuration_$date" + eol + eol);

			tmoCCR.removeRadioEquipmentClockReferenceToBoundaryOrdinaryClock(sb, duInfo);	// [01212021] TC_380
			
			//[10072020]
			sb.append("pr Transport=1,Ptp=1" + eol);
			sb.append("if $nr_of_mos != 0" + eol);
			sb.append("rdel Transport=1,Ptp=1" + eol);
			sb.append("fi" + eol + eol);
			
			sb.append("crn Transport=1,Ptp=1" + eol);
			sb.append("end" + eol + eol);
			
			sb.append("crn Transport=1,Ptp=1,BoundaryOrdinaryClock=1" + eol);
			sb.append("clockType 2" + eol);
			sb.append("domainNumber 24" + eol);
			sb.append("priority1 255" + eol);
			sb.append("priority2 255" + eol);
			sb.append("ptpProfile 2" + eol);
			sb.append("end" + eol + eol);
			sb.append("crn Transport=1,Ptp=1,BoundaryOrdinaryClock=1,PtpBcOcPort=0" + eol);
			sb.append("administrativeState 1" + eol);
			sb.append("announceMessageInterval 1" + eol);
			sb.append("associatedGrandmaster " + eol);
			sb.append("asymmetryCompensation 0" + eol);
			sb.append("dscp 56" + eol);
			sb.append("durationField 300" + eol);
			sb.append("localPriority 128" + eol);
			sb.append("masterOnly false" + eol);
			sb.append("pBit 7" + eol);
			sb.append("ptpMulticastAddress 0" + eol);
			if (duInfo.tmoDUInfo.isIXRERouterType && 		// [11022020] 20.Q3 and newer, IXRE router
		 		  CommonUtil.checkSoftwareGreaterOrEqual(duInfo.softwareLevel, "20.Q3")) {				// [03082021] Updated to generic check of software level
				sb.append("ptpPathTimeError 750" + eol);
			}
			else {
				sb.append("ptpPathTimeError 1000" + eol);
			}
			sb.append("syncMessageInterval -4" + eol);
			sb.append("transportInterface EthernetPort=" + tnPort + eol);
			sb.append("transportVlan" + eol);
			sb.append("end" + eol + eol);
			sb.append("crn Transport=1,Synchronization=1,RadioEquipmentClock=1,RadioEquipmentClockReference=4" + eol);
			sb.append("adminQualityLevel qualityLevelValueOptionI=2,qualityLevelValueOptionII=2,qualityLevelValueOptionIII=1" + eol);
			sb.append("administrativeState 1" + eol);
			sb.append("encapsulation Ptp=1,BoundaryOrdinaryClock=1" + eol);
			sb.append("holdOffTime 1000" + eol);
			String priority ="5"; // Was "4"  [06102020] TC_312
			sb.append("priority " + priority + eol);
			sb.append("useQLFrom 1" + eol);
			sb.append("waitToRestoreTime 60" + eol);
			sb.append("end" + eol + eol);
			sb.append("set SystemFunctions=1,Lm=1,FeatureState=CXC4040008 featureState 1" + eol + eol);
			String dollarSymbol = "$"; 	// [06102020] TC_312
			sb.append("/////////NTP sync Priority set to 3,4 to make it as 3rd sync source///////////////" + eol + eol);
			sb.append("pr Transport=1,Synchronization=1,RadioEquipmentClock=1,RadioEquipmentClockReference=1_2$" + eol);
			sb.append("if $nr_of_mos = 1" + eol);
			sb.append("set Transport=1,Synchronization=1,RadioEquipmentClock=1,RadioEquipmentClockReference=1_2" + dollarSymbol + " priority 4" + eol);
			sb.append("fi" + eol + eol);
			sb.append("pr Transport=1,Synchronization=1,RadioEquipmentClock=1,RadioEquipmentClockReference=1_1$" + eol);
			sb.append("if $nr_of_mos = 1" + eol);
			sb.append("set Transport=1,Synchronization=1,RadioEquipmentClock=1,RadioEquipmentClockReference=1_1" + dollarSymbol + " priority 3" + eol);
			sb.append("fi" + eol + eol);
			sb.append("/////////GPS sync Priority set to 2 to make it as 2nd sync source///////////////" + eol + eol);
			sb.append("pr Transport=1,Synchronization=1,RadioEquipmentClock=1,RadioEquipmentClockReference=1$" + eol);
			sb.append("if $nr_of_mos = 1" + eol);
			sb.append("set Transport=1,Synchronization=1,RadioEquipmentClock=1,RadioEquipmentClockReference=1" + dollarSymbol + " priority 2" + eol);
			sb.append("fi" + eol + eol);
			sb.append("/////////PTP sync Priority set to 1 to make it as primary sync source///////////////" + eol + eol);
			sb.append("set Transport=1,Synchronization=1,RadioEquipmentClock=1,RadioEquipmentClockReference=4" + dollarSymbol + " priority 1" + eol + eol);
			sb.append("cvms Post_PTP_Configuration_$date" + eol + eol);
			
			sb.append("gs-" + eol);
			sb.append("Confbdl-" + eol);
			
			FileUtil.writeToFile(sb, file);
		}
		catch (Exception e) {
			Logger.logger.error("generatePTPSlaveConfigurationScript exception!", e);
			Logger.getGmoLogger().printError("Error generating PTP Slave Configuration Script!");
		}
	}
	
	
	
	private void generate2GPTPSlaveConfigurationScript(SiteCellObj duInfo, String file, String eolType) 
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();
		
		try 
		{			
			String tnPort = "TN_C";
			sb.append("lt all" + eol);
			sb.append("confb+" + eol);
			sb.append(eol);
			sb.append("gs+" + eol);
			sb.append(eol);
			
			sb.append("$date = `date +%y%m%d-%H%M`" + eol);
			sb.append("cvms Pre_PTP_Configuration_$date" + eol);
			
			sb.append("pr Transport=1,Ptp=1" + eol);
			sb.append("if $nr_of_mos != 0" + eol);
			sb.append("rdel Transport=1,Ptp=1" + eol);
			sb.append("fi" + eol + eol);
			
			sb.append("crn Transport=1,Ptp=1" + eol);
			sb.append("end" + eol + eol);
			
			sb.append("crn Transport=1,Ptp=1,BoundaryOrdinaryClock=1" + eol);
			sb.append("clockType 2" + eol);
			sb.append("domainNumber 24" + eol);
			sb.append("priority1 255" + eol);
			sb.append("priority2 255" + eol);
			sb.append("ptpProfile 2" + eol);
			sb.append("end" + eol + eol);
			sb.append("crn Transport=1,Ptp=1,BoundaryOrdinaryClock=1,PtpBcOcPort=0" + eol);
			sb.append("administrativeState 1" + eol);
			sb.append("announceMessageInterval 1" + eol);
			sb.append("associatedGrandmaster " + eol);
			sb.append("asymmetryCompensation 0" + eol);
			sb.append("dscp 56" + eol);
			sb.append("durationField 300" + eol);
			sb.append("localPriority 128" + eol);
			sb.append("masterOnly false" + eol);
			sb.append("pBit 7" + eol);
			sb.append("ptpMulticastAddress 0" + eol);
			sb.append("ptpPathTimeError 750" + eol);
			sb.append("syncMessageInterval -4" + eol);
			sb.append("transportInterface EthernetPort=" + tnPort + eol);
			sb.append("transportVlan" + eol);
			sb.append("end" + eol + eol);

			sb.append("crn Transport=1,Synchronization=1,RadioEquipmentClock=1,RadioEquipmentClockReference=4" + eol);
			sb.append("adminQualityLevel qualityLevelValueOptionI=2,qualityLevelValueOptionII=2,qualityLevelValueOptionIII=1" + eol);
			sb.append("administrativeState 1" + eol);
			sb.append("encapsulation Ptp=1,BoundaryOrdinaryClock=1" + eol);
			sb.append("holdOffTime 1000" + eol);
			String priority ="5"; 
			sb.append("priority " + priority + eol);
			sb.append("useQLFrom 1" + eol);
			sb.append("waitToRestoreTime 60" + eol);
			sb.append("end" + eol + eol);
			sb.append("set SystemFunctions=1,Lm=1,FeatureState=CXC4040008 featureState 1" + eol + eol);
			String dollarSymbol = "$"; 
			sb.append("/////////PTP sync Priority set to 1 to make it as primary sync source///////////////" + eol + eol);
			sb.append("set Transport=1,Synchronization=1,RadioEquipmentClock=1,RadioEquipmentClockReference=4" + dollarSymbol + " priority 1" + eol + eol);
			sb.append("###############OTDOA Decomissioning###############" + eol);
			sb.append("set SystemFunctions=1,Lm=1,FeatureState=CXC4011068 featureState 0" + eol);
			sb.append("set SystemFunctions=1,Lm=1,FeatureState=CXC4011716 featureState 0" + eol);
			sb.append("cvms Post_PTP_Configuration_$date" + eol + eol);		
			
			sb.append("pr Equipment=1,EcBus=1" + eol
					+ "pr Equipment=1,FieldReplaceableUnit=BB-01,EcPort=1" + eol
					+ "if $nr_of_mos != 0" + eol
					+ "set Equipment=1,FieldReplaceableUnit=BB-01,EcPort=1 ecBusRef" + eol
					+ "fi" + eol + eol);
			sb.append("pr Equipment=1,EcBus=1" + eol
					+ "if $nr_of_mos != 0" + eol
					+ "del Equipment=1,EcBus=1" + eol
					+ "fi" + eol + eol + eol);
			sb.append("gs-" + eol);
			sb.append("confb-" + eol);
			
			FileUtil.writeToFile(sb, file);
		}
		catch (Exception e) {
			Logger.logger.error("generate2GPTPSlaveConfigurationScript exception!", e);
			Logger.getGmoLogger().printError("Error generating 2GPTP Slave Configuration Script!");
		}
	}

	/**
	 * Function to generateCabinet1DeletionScript
	 * @param duInfo
	 * @param outputDir
	 * @param eolType
	 */
	// [01272021] Never/No longer used by NSB option. Method copied and adapted for Multi-Du option. See TMO_Config_Change_Recorder
	private void generateCabinet1DeletionScript(SiteCellObj duInfo, String outputDir, String eolType) 
	{
		String eol = StringUtil.getEOL(eolType);
		String file = outputDir + File.separator + "28_" + duInfo.duName + "_BB_Cabinet1_Modification.mos";

		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		StringBuilder sb = new StringBuilder();

		try 
		{
			sb.append("Confbdl+" + eol);
			sb.append("lt all" + eol);
			sb.append(eol);
			sb.append(eol);
			sb.append("################################################################################" + eol);
			sb.append("# Delete all FieldReplaceableUnit with positionRef cabinet=2" + eol);
			sb.append("################################################################################" + eol);
			sb.append(eol);
			sb.append("get Equipment=1,FieldReplaceableUnit positionRef cabinet=2" + eol);
			sb.append("mr fieldunit1" + eol);
			sb.append("ma fieldunit1 Equipment=1,FieldReplaceableUnit positionRef cabinet=2" + eol);
			sb.append(eol);
			sb.append("for $x in fieldunit1" + eol);
			sb.append("rdel $x" + eol);
			sb.append("done" + eol);
			sb.append(eol);
			sb.append("get Equipment=1,FieldReplaceableUnit positionRef cabinet=2" + eol);
			sb.append(eol);
			sb.append("######################################################################################################################" + eol);
			sb.append("# Delete all EquipmentSupportFunction=1,PowerDistribution|Climate|PowerSupply|BatteryBackup controlDomainRef cabinet=2" + eol);
			sb.append("######################################################################################################################" + eol);
			sb.append(eol);
			sb.append("get [EquipmentSupportFunction=1,PowerDistribution|Climate|PowerSupply|BatteryBackup] controlDomainRef cabinet=2" + eol);
			sb.append("mr equipunit1" + eol);
			sb.append("ma equipunit1 [EquipmentSupportFunction=1,PowerDistribution|Climate|PowerSupply|BatteryBackup] controlDomainRef cabinet=2" + eol);
			sb.append(eol);
			sb.append("for $y in equipunit1" + eol);
			sb.append("rdel $y" + eol);
			sb.append("done" + eol);
			sb.append(eol);
			sb.append("get [EquipmentSupportFunction=1,PowerDistribution|Climate|PowerSupply|BatteryBackup] controlDomainRef cabinet=2" + eol);
			sb.append(eol);
			sb.append("################################################################################" + eol);
			sb.append("# Delete Cabinet=2" + eol);
			sb.append("################################################################################" + eol);
			sb.append(eol);
			sb.append("pr Equipment=1,Cabinet=2" + eol);
			sb.append("if $nr_of_mos != 0" + eol);
			sb.append("del Equipment=1,Cabinet=2" + eol);
			sb.append("fi" + eol);
			sb.append(eol);
			sb.append("################################################################################" + eol);
			sb.append("# Deactivate Multicabinet Control feature CXC4011809" + eol);
			sb.append("################################################################################" + eol);
			sb.append(eol);
			sb.append("lset SystemFunctions=1,Lm=1,FeatureState=CXC4011809 featureState 0" + eol);
			sb.append(eol);
			sb.append("################################################################################" + eol);
			sb.append("# Setting AutoCreateunit to true" + eol);
			sb.append("################################################################################" + eol);
			sb.append(eol);
			sb.append("lset EquipmentSupportFunction=1 autoCreateUnits true" + eol);
			sb.append(eol);
			sb.append("mr fieldunit1" + eol);
			sb.append("mr equipunit1" + eol);
			sb.append(eol);
			sb.append(eol);
			sb.append("Confbdl-" + eol);

			FileUtil.writeToFile(sb, file);
		}
		catch (Exception e) {
			Logger.logger.error("generateCabinet1DeletionScript exception!", e);
			Logger.getGmoLogger().printError("Error generating Cabinet 1 Deletion Script!");
		}
	}
	

	/**
	 * Function to generate Cabinet 2 modification block using Parameter preservation in anchor node
	 * @param duInfo
	 * @param duNameOld
	 * @param outputDir
	 * @param pp
	 * @param eolType
	 */
	// [01272021] Never/No longer used by NSB option. Method copied and adapted for Multi-Du option. See TMO_Config_Change_Recorder
	private void generateCabinet2ModificationBlock(SiteCellObj duInfo, String duNameOld, String outputDir, ParamPreservation pp, String eolType) {
		String eol = StringUtil.getEOL(eolType);
		StringBuilder sb = new StringBuilder();

		String file = outputDir + File.separator + "41_" + duInfo.duName + "_BB_Cabinet2_Modification.mos";
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		
		Set<String> moCreatedTracker = new HashSet<String>();
		try {
			Map<String, SiteCellObj> duToDUInfo = tmoCCR.getDUToDUInfo();
			SiteCellObj duInfoOld = new SiteCellObj();
			if (duToDUInfo.containsKey(duNameOld)) {
				duInfoOld = duToDUInfo.get(duNameOld);
			}
			else {
				Logger.getGmoLogger().printError("Can not find data for original node for cabinet 2 " + duNameOld);
			}
			
			sb.append("confbdl+" + eol);
			sb.append("gs+" + eol + eol + eol);
			sb.append("lt all" + eol + eol);
			sb.append("lset EquipmentSupportFunction=1 autoCreateUnits false" + eol);
			sb.append("lset EquipmentSupportFunction=1 supportSystemControl true" + eol + eol);
			
			List<String> ignoreList = new ArrayList<String>();
			List<String> includeList = new ArrayList<String>();
			
			//Cabinet
			StringBuilder sbCabinet = new StringBuilder();
			ArrayList<HashMap<String, String>> cabinetDataArray = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getKGETCSVFile("Cabinet"), "NodeMOKey", duNameOld + "!.*");
			List<String> cabinet2ReservedByList = new ArrayList<String>();
			ignoreList.add("sharedCabinetIdentifier");
			for (int index=0; index < cabinetDataArray.size(); index++) {
				HashMap<String, String> cabinetHashMap = new HashMap<String, String>(cabinetDataArray.get(index));
				String cabinetId = CommonUtil.getValueFromRegexKey(cabinetHashMap, "CabinetId");
				if (cabinetId.matches("2")) {
					String cabinet2ReservedByStr = CommonUtil.getValueFromRegexKey(cabinetHashMap, "reservedBy");
					
					for (String reservedByMo : cabinet2ReservedByStr.split(";")) {
						cabinet2ReservedByList.add(reservedByMo);
					}
					
					String ldn = "Equipment=1,Cabinet=1";
					String sharedCabinetIdentifier = CommonUtil.getValueFromRegexKey(cabinetHashMap, "sharedCabinetIdentifier").replace("2", "1");		// Cabinet_2 -> Cabinet_1
					if(!cabinet2ReservedByList.isEmpty() && !moCreatedTracker.contains(ldn)) {
						sbCabinet.append("pr " + ldn + "$" + eol);
						sbCabinet.append("if $nr_of_mos = 0" + eol);
						sbCabinet.append("crn " + ldn + eol);
						pp.preserveAllParamWithDefaultKeepingMandatory(duInfo, sbCabinet, cabinetHashMap, "Cabinet", String.join("|", ignoreList), String.join("|", includeList), "", eol);
						sbCabinet.append("sharedCabinetIdentifier " + sharedCabinetIdentifier + eol);
						sbCabinet.append("end" + eol);
						sbCabinet.append("fi" + eol + eol);
						sbCabinet.append("lset Equipment=1,Cabinet=1 climateSystem " + cabinetHashMap.get("climateSystem").replaceAll("[\\s].*", "") + eol);
						sbCabinet.append("lset Equipment=1,Cabinet=1 climateRegulationSystem " + cabinetHashMap.get("climateRegulationSystem").replaceAll("[\\s].*", "") + eol);
						sbCabinet.append("lset Equipment=1,Cabinet=1 smokeDetector " + cabinetHashMap.get("smokeDetector").toLowerCase() + eol + eol);
						
						moCreatedTracker.add(ldn);
					}
				}
			}
			sb.append(sbCabinet.toString());

			
			if(!cabinet2ReservedByList.isEmpty()) {
				//Climate
				StringBuilder sbClimate = new StringBuilder();
				ArrayList<HashMap<String, String>> climateDataArray = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getKGETCSVFile("Climate"), "NodeMOKey", duNameOld + "!.*");
				for (int index=0; index < climateDataArray.size(); index++) {
					HashMap<String, String> climateHashMap = new HashMap<String, String>(climateDataArray.get(index));
					String climateMo = CommonUtil.getValueFromRegexKey(climateHashMap, "MO").replaceAll(".*,Equipment", "Equipment");		// EquipmentSupportFunction=1,Climate=2
					String climateControlMode = CommonUtil.getValueFromRegexKey(climateHashMap, "climateControlMode");
					String ldn = "EquipmentSupportFunction=1,Climate=1";
					if (cabinet2ReservedByList.contains(climateMo) && !moCreatedTracker.contains(ldn)) {
						sbClimate.append("pr " + ldn + "$" + eol);
						sbClimate.append("if $nr_of_mos = 0" + eol);
						sbClimate.append("cr " + ldn + eol);
						sbClimate.append("fi" + eol + eol);
						sbClimate.append("set EquipmentSupportFunction=1,Climate=1 controlDomainRef Equipment=1,Cabinet=1" + eol);
						if (!climateControlMode.isEmpty())
						sbClimate.append("lset EquipmentSupportFunction=1,Climate=1 climateControlMode " + climateControlMode + eol);
						sbClimate.append(eol);

						moCreatedTracker.add(ldn);
					}
				}
				sb.append(sbClimate.toString());
				
				//PowerSupply
				StringBuilder sbPowerSupply = new StringBuilder();
				ArrayList<HashMap<String, String>> powerSupplyDataArray = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getKGETCSVFile("PowerSupply"), "NodeMOKey", duNameOld + "!.*");
				for (int index=0; index < powerSupplyDataArray.size(); index++) {
					HashMap<String, String> powerSupplyHashMap = new HashMap<String, String>(powerSupplyDataArray.get(index));
					String powerSupplyMo = CommonUtil.getValueFromRegexKey(powerSupplyHashMap, "MO").replaceAll(".*,Equipment", "Equipment");		// EquipmentSupportFunction=1,PowerSupply=2
					String ldn = "EquipmentSupportFunction=1,PowerSupply=1";
					if (cabinet2ReservedByList.contains(powerSupplyMo) && !moCreatedTracker.contains(ldn)) {
						sbPowerSupply.append("pr " + ldn + "$" + eol);
						sbPowerSupply.append("if $nr_of_mos = 0" + eol);
						sbPowerSupply.append("cr " + ldn + eol);
						sbPowerSupply.append("fi" + eol + eol);

						moCreatedTracker.add(ldn);
					}
				}
				sb.append(sbPowerSupply.toString());
				
				//PowerDistribution
				StringBuilder sbPowerDistribution = new StringBuilder();
				ArrayList<HashMap<String, String>> powerDistributionDataArray = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getKGETCSVFile("PowerDistribution"), "NodeMOKey", duNameOld + "!.*");
				for (int index=0; index < powerDistributionDataArray.size(); index++) {
					HashMap<String, String> powerDistributionHashMap = new HashMap<String, String>(powerDistributionDataArray.get(index));
					String powerDistributionMo = CommonUtil.getValueFromRegexKey(powerDistributionHashMap, "MO").replaceAll(".*,Equipment", "Equipment");		// EquipmentSupportFunction=1,PowerDistribution=2
					String ldn = "EquipmentSupportFunction=1,PowerDistribution=1";
					if (cabinet2ReservedByList.contains(powerDistributionMo) && !moCreatedTracker.contains(ldn)) {
						sbPowerDistribution.append("pr " + ldn + "$" + eol);
						sbPowerDistribution.append("if $nr_of_mos = 0" + eol);
						sbPowerDistribution.append("cr " + ldn + eol);
						sbPowerDistribution.append("fi" + eol + eol);

						moCreatedTracker.add(ldn);
					}
				}
				sb.append(sbPowerDistribution.toString());
				
				//BatteryBackup
				StringBuilder sbBatteryBackup = new StringBuilder();
				ArrayList<HashMap<String, String>> batteryBackupDataArray = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getKGETCSVFile("BatteryBackup"), "NodeMOKey", duNameOld + "!.*");
				for (int index=0; index < batteryBackupDataArray.size(); index++) {
					HashMap<String, String> batteryBackupHashMap = new HashMap<String, String>(batteryBackupDataArray.get(index));
					String batteryBackupMo = CommonUtil.getValueFromRegexKey(batteryBackupHashMap, "MO").replaceAll(".*,Equipment", "Equipment");		// EquipmentSupportFunction=1,BatteryBackup=2
					String ldn = "EquipmentSupportFunction=1,BatteryBackup=1";
					if (cabinet2ReservedByList.contains(batteryBackupMo) && !moCreatedTracker.contains(ldn)) {
						sbBatteryBackup.append("pr " + ldn + "$" + eol);
						sbBatteryBackup.append("if $nr_of_mos = 0" + eol);
						sbBatteryBackup.append("cr " + ldn + eol);
						sbBatteryBackup.append("fi" + eol + eol);

						moCreatedTracker.add(ldn);
					}
				}
				sb.append(sbBatteryBackup.toString());
				
				sb.append("set . controlDomainRef Equipment=1,Cabinet=1" + eol);
				sb.append(eol + eol);
				sb.append("WAIT 10" + eol);
				sb.append(eol + eol + eol);
				sb.append("## Create HWunit" + eol);
				sb.append("########################" + eol);
				sb.append(eol + eol);
				sb.append("// FieldReplaceableUnit" + eol);
				
				//FieldReplaceableUnit
				StringBuilder sbFieldReplaceableUnit = new StringBuilder();
				ArrayList<HashMap<String, String>> fieldReplaceableUnitDataArray = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getKGETCSVFile("FieldReplaceableUnit"), "NodeMOKey", duNameOld + "!.*");
				ignoreList.add("positionRef");
				ignoreList.add("floorInformation");
				for (int index=0; index < fieldReplaceableUnitDataArray.size(); index++) {
					HashMap<String, String> fieldReplaceableUnitHashMap = new HashMap<String, String>(fieldReplaceableUnitDataArray.get(index));
					String fieldReplaceableUnitMo = CommonUtil.getValueFromRegexKey(fieldReplaceableUnitHashMap, "MO").replaceAll(".*,Equipment", "Equipment");		// Equipment=1,FieldReplaceableUnit=PSU-9
					if (cabinet2ReservedByList.contains(fieldReplaceableUnitMo)) {
						String fieldReplaceableUnitId = CommonUtil.getValueFromRegexKey(fieldReplaceableUnitHashMap, "FieldReplaceableUnitId");
						String ldn = "Equipment=1,FieldReplaceableUnit=" + fieldReplaceableUnitId;
						String positionRef = CommonUtil.getValueFromRegexKey(fieldReplaceableUnitHashMap, "positionRef").replaceAll(".*,", "").replace("Cabinet=2", "Cabinet=1");
						if(!fieldReplaceableUnitId.isEmpty() && !moCreatedTracker.contains(ldn)) {
							sbFieldReplaceableUnit.append("pr " + ldn + "$" + eol);
							sbFieldReplaceableUnit.append("if $nr_of_mos = 0" + eol);
							sbFieldReplaceableUnit.append("crn " + ldn + eol);
							pp.preserveAllParamWithDefaultKeepingMandatory(duInfo, sbFieldReplaceableUnit, fieldReplaceableUnitHashMap, "FieldReplaceableUnit", String.join("|", ignoreList), String.join("|", includeList), "", eol);
							sbFieldReplaceableUnit.append("positionRef " + positionRef + eol);
							sbFieldReplaceableUnit.append("end" + eol);
							sbFieldReplaceableUnit.append("fi" + eol + eol);
							
							moCreatedTracker.add(ldn);
						}
					}
				}
				sb.append(sbFieldReplaceableUnit.toString());
				
	
				//EcPort
				StringBuilder sbEcPort = new StringBuilder();
				ArrayList<HashMap<String, String>> ecPortDataArray = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getKGETCSVFile("EcPort"), "NodeMOKey", duNameOld + "!.*");
				ignoreList.add("ecBusRef");
				for (int index=0; index < ecPortDataArray.size(); index++) {
					HashMap<String, String> ecPortHashMap = new HashMap<String, String>(ecPortDataArray.get(index));
					String ecPortMo = CommonUtil.getValueFromRegexKey(ecPortHashMap, "MO").replaceAll(".*,Equipment", "Equipment");		// Equipment=1,FieldReplaceableUnit=PSU-9,EcPort=1
					String fieldReplaceableUnitMo = ecPortMo.replaceAll(",EcPort.*", "");												// Equipment=1,FieldReplaceableUnit=PSU-9
					if (cabinet2ReservedByList.contains(fieldReplaceableUnitMo)) {
						String ecPortId = CommonUtil.getValueFromRegexKey(ecPortHashMap, "EcPortId");
						String fieldReplaceableUnitId = fieldReplaceableUnitMo.replaceAll(".*=", "");
						String ldn = "Equipment=1,FieldReplaceableUnit=" + fieldReplaceableUnitId + ",EcPort=" + ecPortId;
						String ecBusRef = CommonUtil.getValueFromRegexKey(ecPortHashMap, "ecBusRef").replaceAll(".*,", "").replace("EcBus=2", "EcBus=1");
						if(!ecPortId.isEmpty() && !moCreatedTracker.contains(ldn)) {
							sbEcPort.append("pr " + ldn + "$" + eol);
							sbEcPort.append("if $nr_of_mos = 0" + eol);
							sbEcPort.append("crn " + ldn + eol);
							pp.preserveAllParamWithDefaultKeepingMandatory(duInfo, sbEcPort, ecPortHashMap, "EcPort", String.join("|", ignoreList), String.join("|", includeList), "", eol);
							sbEcPort.append("ecBusRef " + ecBusRef + eol);
							sbEcPort.append("end" + eol);
							sbEcPort.append("fi" + eol + eol);
							
							moCreatedTracker.add(ldn);
						}
					}
				}
				sb.append(sbEcPort.toString());
			
				sbEcPort = new StringBuilder();
				for (int index=0; index < ecPortDataArray.size(); index++) {
					HashMap<String, String> ecPortHashMap = new HashMap<String, String>(ecPortDataArray.get(index));
					String ecPortMo = CommonUtil.getValueFromRegexKey(ecPortHashMap, "MO").replaceAll(".*,Equipment", "Equipment");		// Equipment=1,ExternalNode=1,EcPort=1
					String externalNodeMo = ecPortMo.replaceAll(",EcPort.*", "");														// Equipment=1,ExternalNode=1
					if (!cabinet2ReservedByList.contains(externalNodeMo) && externalNodeMo.contains("ExternalNode")) {					// MO is not a FieldReplaceableUnit
						String ecPortId = CommonUtil.getValueFromRegexKey(ecPortHashMap, "EcPortId");
						String externalNodeId = externalNodeMo.replaceAll(".*=", "");
						String ldn = "Equipment=1,ExternalNode=" + externalNodeId + ",EcPort=" + ecPortId;
						String ecBusRef = CommonUtil.getValueFromRegexKey(ecPortHashMap, "ecBusRef").replaceAll(".*,", "");
						String prefix = ecBusRef.contains("EcBus=2") ? "" : "//";		// Comment out command if no change needed
						ecBusRef = ecBusRef.replace("EcBus=2", "EcBus=1");
						if(!ecPortId.isEmpty() && !moCreatedTracker.contains(ldn)) {
							sbEcPort.append(prefix + "pr " + ldn + "$" + eol);
							sbEcPort.append(prefix + "if $nr_of_mos = 0" + eol);
							sbEcPort.append(prefix + "crn " + ldn + eol);
							sbEcPort.append(prefix + "ecBusRef " + ecBusRef + eol);
							pp.preserveAllParamWithDefaultKeepingMandatory(duInfo, sbEcPort, ecPortHashMap, "EcPort", String.join("|", ignoreList), String.join("|", includeList), prefix, eol);
							sbEcPort.append(prefix + "end" + eol);
							sbEcPort.append(prefix + "fi" + eol + eol);
							
							moCreatedTracker.add(ldn);
						}
					}
				}
				sb.append(sbEcPort.toString());
				
				
				//AlarmPort
				StringBuilder sbSauAlarmPort = new StringBuilder();
				ArrayList<HashMap<String, String>> alarmPortDataArray = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getKGETCSVFile("AlarmPort"), "NodeMOKey", duNameOld + "!.*");
				for (int index=0; index < alarmPortDataArray.size(); index++) {
					HashMap<String, String> alarmPortHashMap = new HashMap<String, String>(alarmPortDataArray.get(index));
					String alarmPortMo = CommonUtil.getValueFromRegexKey(alarmPortHashMap, "MO").replaceAll(".*,Equipment", "Equipment");	// Equipment=1,FieldReplaceableUnit=SAU-2,AlarmPort=1
					String alarmPortId = CommonUtil.getValueFromRegexKey(alarmPortHashMap, "AlarmPortId");
					String fieldReplaceableUnitMo = alarmPortMo.replaceAll(",AlarmPort.*", "");												// Equipment=1,FieldReplaceableUnit=SAU-2
					String fieldReplaceableUnitId = fieldReplaceableUnitMo.replaceAll(".*=", "");
					if (cabinet2ReservedByList.contains(fieldReplaceableUnitMo) && fieldReplaceableUnitId.contains("SAU")) {
						String ldn = "FieldReplaceableUnit=" + fieldReplaceableUnitId + ",AlarmPort=" + alarmPortId;
						if (!alarmPortId.isEmpty() && !moCreatedTracker.contains(ldn)) {
							sbSauAlarmPort.append("pr " + ldn + "$" + eol);
							sbSauAlarmPort.append("if $nr_of_mos = 0" + eol);
							sbSauAlarmPort.append("cr " + ldn + eol);
							sbSauAlarmPort.append("fi" + eol + eol);

							moCreatedTracker.add(ldn);
						}
					}
				}
				if (!sbSauAlarmPort.toString().isEmpty()) {
					sb.append("############################################################" + eol);
					sb.append("## Create SAU AlarmPort" + eol);
					sb.append("############################################################" + eol);
					sb.append(eol);
				}
				sb.append(sbSauAlarmPort.toString());

				
				StringBuilder sbScuAlarmPort = new StringBuilder();
				for (int index=0; index < alarmPortDataArray.size(); index++) {
					HashMap<String, String> alarmPortHashMap = new HashMap<String, String>(alarmPortDataArray.get(index));
					String alarmPortMo = CommonUtil.getValueFromRegexKey(alarmPortHashMap, "MO").replaceAll(".*,Equipment", "Equipment");	// Equipment=1,FieldReplaceableUnit=SAU-2,AlarmPort=1
					String alarmPortId = CommonUtil.getValueFromRegexKey(alarmPortHashMap, "AlarmPortId");
					String fieldReplaceableUnitMo = alarmPortMo.replaceAll(",AlarmPort.*", "");												// Equipment=1,FieldReplaceableUnit=SAU-2
					String fieldReplaceableUnitId = fieldReplaceableUnitMo.replaceAll(".*=", "");
					if (cabinet2ReservedByList.contains(fieldReplaceableUnitMo) && fieldReplaceableUnitId.contains("SCU")) {
						String ldn = "FieldReplaceableUnit=" + fieldReplaceableUnitId + ",AlarmPort=" + alarmPortId;
						if (!alarmPortId.isEmpty() && !moCreatedTracker.contains(ldn)) {
							sbScuAlarmPort.append("pr " + ldn + "$" + eol);
							sbScuAlarmPort.append("if $nr_of_mos = 0" + eol);
							sbScuAlarmPort.append("cr " + ldn + eol);
							sbScuAlarmPort.append("fi" + eol + eol);

							moCreatedTracker.add(ldn);
						}
					}
				}
				if (!sbScuAlarmPort.toString().isEmpty()) {
					sb.append("############################################################" + eol);
					sb.append("## Create SCU AlarmPort" + eol);
					sb.append("############################################################" + eol);
					sb.append(eol);
				}
				sb.append(sbScuAlarmPort.toString());
				
				
				StringBuilder sbAlarmSlogan = new StringBuilder();
				ignoreList.add("administrativeState");
				ignoreList.add("alarmSlogan");
				for (int index=0; index < alarmPortDataArray.size(); index++) {
					HashMap<String, String> alarmPortHashMap = new HashMap<String, String>(alarmPortDataArray.get(index));
					String alarmPortMo = CommonUtil.getValueFromRegexKey(alarmPortHashMap, "MO").replaceAll(".*,Equipment", "Equipment");	// Equipment=1,FieldReplaceableUnit=SAU-2,AlarmPort=1
					String alarmPortId = CommonUtil.getValueFromRegexKey(alarmPortHashMap, "AlarmPortId");
					String fieldReplaceableUnitMo = alarmPortMo.replaceAll(",AlarmPort.*", "");												// Equipment=1,FieldReplaceableUnit=SAU-2
					String fieldReplaceableUnitId = fieldReplaceableUnitMo.replaceAll(".*=", "");
					if (cabinet2ReservedByList.contains(fieldReplaceableUnitMo) && fieldReplaceableUnitId.contains("SAU")) {
						String ldn = "Equipment=1,FieldReplaceableUnit=" + fieldReplaceableUnitId + ",AlarmPort=" + alarmPortId;
						String administrativeState = CommonUtil.getValueFromRegexKey(alarmPortHashMap, "administrativeState").replaceAll("[\\s].*", "");
						String alarmSlogan = CommonUtil.getValueFromRegexKey(alarmPortHashMap, "alarmSlogan");
//						String perceivedSeverity = CommonUtil.getValueFromRegexKey(alarmPortHashMap, "perceivedSeverity").replaceAll("[\\s].*", "");
//						String normallyOpen = CommonUtil.getValueFromRegexKey(alarmPortHashMap, "normallyOpen").toLowerCase();
						if (!alarmPortId.isEmpty() && !alarmSlogan.isEmpty() && !moCreatedTracker.contains(ldn)) {
							sbAlarmSlogan.append("lset " + ldn + "$ administrativeState 0" + eol);
							sbAlarmSlogan.append("lset " + ldn + "$ alarmSlogan " + alarmSlogan + eol);
//							sbAlarmSlogan.append("lset " + ldn + "$ perceivedSeverity " + perceivedSeverity + eol);
//							sbAlarmSlogan.append("lset " + ldn + "$ normallyOpen " + normallyOpen + eol);
							pp.preserveAllParamWithDefaultKeepingMandatory(duInfo, sbAlarmSlogan, alarmPortHashMap, "AlarmPort", String.join("|", ignoreList), String.join("|", includeList), "lset " + ldn + "$", eol);
							sbAlarmSlogan.append("lset " + ldn + "$ administrativeState " + administrativeState + eol + eol);

							moCreatedTracker.add(ldn);
						}
					}
				}
				if (!sbAlarmSlogan.toString().isEmpty()) {
					sb.append("######################################" + eol);
					sb.append("## Define SAU AlarmSlogan" + eol);
					sb.append("######################################" + eol);
					sb.append(eol);
				}
				sb.append(sbAlarmSlogan.toString());
				
				
				StringBuilder sbEFuseUserLabel = new StringBuilder();
				ArrayList<HashMap<String, String>> eFuseDataArray = CSVUtils.readDataRowArrayFromCSVFile(CSVUtils.getKGETCSVFile("EFuse"), "NodeMOKey", duNameOld + "!.*");
				ignoreList = new ArrayList<String>();
				for (int index=0; index < eFuseDataArray.size(); index++) {
					HashMap<String, String> eFuseHashMap = new HashMap<String, String>(eFuseDataArray.get(index));
					String eFuseMo = CommonUtil.getValueFromRegexKey(eFuseHashMap, "MO").replaceAll(".*,Equipment", "Equipment");	// Equipment=1,FieldReplaceableUnit=PDU-8,EFuse=4
					String eFuseId = CommonUtil.getValueFromRegexKey(eFuseHashMap, "EFuseId");
					String fieldReplaceableUnitMo = eFuseMo.replaceAll(",EFuse.*", "");												// Equipment=1,FieldReplaceableUnit=PDU-8
					String fieldReplaceableUnitId = fieldReplaceableUnitMo.replaceAll(".*=", "");
					if (cabinet2ReservedByList.contains(fieldReplaceableUnitMo) && fieldReplaceableUnitId.contains("PDU")) {
						String ldn = "Equipment=1,FieldReplaceableUnit=" + fieldReplaceableUnitId + ",EFuse=" + eFuseId;
//						String userLabel = CommonUtil.getValueFromRegexKey(eFuseHashMap, "userLabel");
						if (!eFuseId.isEmpty() && !moCreatedTracker.contains(ldn)) {
							pp.preserveAllParamWithDefaultKeepingMandatory(duInfo, sbEFuseUserLabel, eFuseHashMap, "EFuse", String.join("|", ignoreList), String.join("|", includeList), "lset " + ldn + "$", eol);
//							sbEFuseUserLabel.append("lset " + ldn + "$ userLabel " + userLabel + eol);

							moCreatedTracker.add(ldn);
						}
					}
				}
				if (!sbEFuseUserLabel.toString().isEmpty()) {
					sb.append("############################################################" + eol);
					sb.append("## Define PDU Label" + eol);
					sb.append("############################################################" + eol);
					sb.append(eol);
				}
				sb.append(sbEFuseUserLabel.toString());
			}
		
			
			sb.append(eol + eol);
			sb.append("################################################################################" + eol);
			sb.append("# Setting AutoCreateunit to true" + eol);
			sb.append("################################################################################" + eol + eol);
			sb.append("lset EquipmentSupportFunction=1 autoCreateUnits true" + eol + eol);
			sb.append("gs-" + eol);
			sb.append("confbdl" + eol);

			FileUtil.writeToFile(sb, file);
		}
		catch (Exception e) {
			Logger.logger.error("generateCabinet2ModificationBlock exception!", e);
			Logger.getGmoLogger().printError("Generate Cabinet 2 Modification block for " + duInfo.duName);
		}
	}
	
	
	/**
	 * Function to generate SWInfo CSV file
	 */
	private void generateSWInfoCSVFile()
	{
		boolean blnNewSwInfoLogicHasError = false;
		
		// define an arraylist to hold SWInfo data.
		ArrayList<String> csvArrayList = new ArrayList<String>();
//		{
//			csvArrayList.add("Node_Name,Customer,GMO_User_Name,Added_Date,SW_Level_Major,SW_Level_Minor,EAMS_ID,Src_SW_Level_Major,Src_SW_Level_Minor");
//		}
//		else {
			csvArrayList.add("Node_Name,Customer,GMO_User_Name,Added_Date,SW_Level_Major,SW_Level_Minor,EAMS_ID,ECM_Capable");
//		}

		Logger.getGmoLogger().printTextWithTimeStamp("Extracting SW level info...");
		try {
			// determine the datetime format.
			SimpleDateFormat sdf = new SimpleDateFormat("MM/dd/yyyy HH:mm:ss a");

			// set the timezone to be CST
			sdf.setTimeZone(TimeZone.getTimeZone("CST"));

			// get current date time and convert it to the timezone specified
			String dateTimeForCsv = sdf.format(new Date());

			Hashtable<String, String> siteToEAMSIdHash = new Hashtable<String, String>();
			siteToEAMSIdHash = Tools.getLkfStatusWithEAMSId(new File(siteList));
			ArrayList<String> lstNodesAlreadyCaptured = new ArrayList<String>();

			for(Map.Entry<String, String> kvp : siteToEAMSIdHash.entrySet()) {
				String EAMSId = "0";
				try {
					EAMSId = kvp.getValue();
					if (EAMSId == null) {
						Logger.getGmoLogger().printError("EAMS Id not found for site " + kvp.getKey() + ". Setting it to 0.");
						EAMSId = "0";
					}
					else if (EAMSId.equals("")) {
						EAMSId = "0";
					}
				}
				catch (Exception ex) {
					// the site was not found in EAMS, hence no EAMS ID retrieved.
					Logger.getGmoLogger().printError("EAMS Id not found for site " + kvp.getKey() + ".");
				}

				String strTgtCurrSwLevelMaj = "na", strTgtCurrSwLevelMin = "na";
				// get the sw levels from the recorder

				SiteCellObj objSiteInfo =  tmoCCR.getDUToDUInfo().get(kvp.getKey());
				
				try {
//					{	// [10232020] swapped which object to check first as nodeInfo has different format for values
//						strTgtCurrSwLevelMaj = objSiteInfo.nodeInfoObj.softwareLevel;
//						strTgtCurrSwLevelMin = objSiteInfo.nodeInfoObj.upgradePackageName;
//					}
//					else {
					strTgtCurrSwLevelMaj = objSiteInfo.softwareLevel;
					strTgtCurrSwLevelMin = objSiteInfo.pciSiteObj.upgradePackageId;
//					}
				}
				catch(Exception ex) {
					strTgtCurrSwLevelMaj = "";
					strTgtCurrSwLevelMin = "";	
				}

				// get from kget
				if(strTgtCurrSwLevelMaj.equals("") || strTgtCurrSwLevelMin.equals("")){
					try {
						objSiteInfo =  tmoCCR.getDUToDUInfo().get(kvp.getKey());

						// [10232020] swapped which object to check first as nodeInfo has different format for values
//						strTgtCurrSwLevelMaj = objSiteInfo.softwareLevel;
//						strTgtCurrSwLevelMin = objSiteInfo.pciSiteObj.upgradePackageId;
						strTgtCurrSwLevelMaj = objSiteInfo.nodeInfoObj.softwareLevel;
						strTgtCurrSwLevelMin = objSiteInfo.nodeInfoObj.upgradePackageName;
					}
					catch(Exception ex) {
						strTgtCurrSwLevelMaj = "";
						strTgtCurrSwLevelMin = "";
					}
				}
				
				if ((strTgtCurrSwLevelMaj == null) || (strTgtCurrSwLevelMaj.trim().equals("na")) || (strTgtCurrSwLevelMaj.trim().equals(""))) {
					strTgtCurrSwLevelMaj = "na";
				}
				if ((strTgtCurrSwLevelMin == null) || (strTgtCurrSwLevelMin.trim().equals("na")) || (strTgtCurrSwLevelMin.trim().equals(""))) {
					strTgtCurrSwLevelMin = "na";
				}

				// [10232020]
//				strTgtCurrSwLevelMaj = strTgtCurrSwLevelMaj.replace("/", "_").replace("-", "_").replace("%", "_");
//				strTgtCurrSwLevelMin = strTgtCurrSwLevelMin.replace("/", "_").replace("-", "_").replace("%", "_");
				strTgtCurrSwLevelMaj = strTgtCurrSwLevelMaj.replaceAll("[\\W]+", "_");	// Replace any non-alphanumeric char, such as "\", " ", "-" with under_score
				strTgtCurrSwLevelMin = strTgtCurrSwLevelMin.replaceAll("[\\W]+", "_");	// Replace any non-alphanumeric char, such as "\", " ", "-" with under_score

				strTgtCurrSwLevelMin = strTgtCurrSwLevelMin.replaceAll("RadioNode_", "").replaceAll("_" + strTgtCurrSwLevelMaj, "");	// Just in case NSB version was stored such as 'RadioNode_CXP9024418_15_R13D61_20.Q3' should be 'CXP9024418_15_R13D61'

				if(objSiteInfo.isNewSite) {
					objSiteInfo.isecmcapable = true;
				}
				
				if(objSiteInfo.tmoDUInfo.isMidBandAnchorScope || objSiteInfo.tmoDUInfo.isMidBandAnchorScopeWith6449Radio) {	// [10192020]
//					if (objSiteInfo.getSiteObj().isIs4gAnchor()) {	// [11032020] For now, make B41 not ecmCapable from both NSB and Multi-Du options
//						objSiteInfo.isecmcapable = false;
//					}
					objSiteInfo.isecmcapable = true;
				}
				
				String strNodeNameFoSwInfoDb = kvp.getKey();
				
				if(objSiteInfo.tmoDUInfo.isMixedModeBasebandScope) {
					if((objSiteInfo.duName.startsWith("N")) ||
					   (objSiteInfo.duName.startsWith("M")))	{
						objSiteInfo.isecmcapable = true;
						
						// update the 'M' node name to 'N' node name for SW Info DB.
						if (!objSiteInfo.isNewSite) {	// [10232020] New MMBB site name must match CIQ, will always start with M if new
							strNodeNameFoSwInfoDb = "N" + objSiteInfo.duName.substring(1);
							
							// get the actual N node name from the kget (because it may be N, N2, N3, N4 etc)
							String gnbNodeNameFromKget = CSVUtils.readDataFromCSVFile(CSVUtils.getKGETCSVFile("GNBDUFunction"), "gNBId", objSiteInfo.tmoDUInfo.gNBIdTND, "NodeMOKey");
							gnbNodeNameFromKget = gnbNodeNameFromKget.replaceAll("!.*", "");
							if (!gnbNodeNameFromKget.isEmpty()) {
								strNodeNameFoSwInfoDb = gnbNodeNameFromKget.toString();
							}
						}
					}
					else {
						objSiteInfo.isecmcapable = false;
					}
					
					if(EAMSId != null && EAMSId.equals("0")) {
						ArrayList<String> lst = new ArrayList<String>();
						lst.add(strNodeNameFoSwInfoDb);
						Hashtable<String, String> newS2GMap = S2GUtils.getLatestS2gId(lst);
						if(newS2GMap.get(strNodeNameFoSwInfoDb) != null) {
							EAMSId = newS2GMap.get(strNodeNameFoSwInfoDb);
						}
					}
				}
				
				if(objSiteInfo.tmoDUInfo.isTDDMixedModeBaseBandScope) {// For TDD MMBB
					if(objSiteInfo.tmoDUInfo.isMidBandTddMMBBVariation) {
						objSiteInfo.isecmcapable = true;
					}
					else {
						objSiteInfo.isecmcapable = false;
					}
				}
				
				if(objSiteInfo.tmoDUInfo.isLowBandMidBandMixedModeBaseBandScope) {
					if(objSiteInfo.tmoDUInfo.isLowBandMMBBVariation || objSiteInfo.tmoDUInfo.isMidBandTddMMBBVariation) {
						objSiteInfo.isecmcapable = true;
					}
					else {
						objSiteInfo.isecmcapable = false;
					}
				}
				
				if(objSiteInfo.tmoDUInfo.isNewLowBandAndLiveMidBandMixedModeBaseBandScope) {
					if(objSiteInfo.tmoDUInfo.isLowBandMMBBVariation) {
						objSiteInfo.isecmcapable = true;
					}
					else {
						objSiteInfo.isecmcapable = false;
					}
				}
				
				if(objSiteInfo.tmoDUInfo.isMidBandTdd2CAddMixedModeBaseBandScope || objSiteInfo.tmoDUInfo.isLiveLowBandAndTdd2CAddMixedModeBaseBandScope) {
					if(objSiteInfo.tmoDUInfo.isMidBandTddMMBBVariation) {
						objSiteInfo.isecmcapable = true;
					}
					else {
						objSiteInfo.isecmcapable = false;
					}
				}
				
				if(objSiteInfo.tmoDUInfo.isNewLowBandAndTdd2CAddMixedModeBaseBandScope) {
					if(objSiteInfo.tmoDUInfo.isMidBandTddMMBBVariation || objSiteInfo.tmoDUInfo.isLowBandMMBBVariation) {
						objSiteInfo.isecmcapable = true;
					}
					else {
						objSiteInfo.isecmcapable = false;
					}
				}
				
				if(objSiteInfo.tmoDUInfo.isMidbandMixedModeBasebandScope) {
					if(objSiteInfo.tmoDUInfo.isMidBandFddMMBBVariation && objSiteInfo.nodeBandType.equals("N66"))
						objSiteInfo.isecmcapable = true;
					else
						objSiteInfo.isecmcapable = false;
				}
				
				if(objSiteInfo.tmoDUInfo.isSetUp1DReconfig) {
					if(objSiteInfo.duName.startsWith("M")) {
						objSiteInfo.isecmcapable = true;
					}
					else {
						objSiteInfo.isecmcapable = false;
					}
				}
				
				if(objSiteInfo.tmoDUInfo.isTddCarrierAddScope) {	// [122021] GMO_TMO-206, NR or MMBB TDD 2C add is ecmcapable 
					objSiteInfo.isecmcapable = true;
				}
				
				if (!objSiteInfo.criticalErrors.isEmpty() || (strTgtCurrSwLevelMaj.contains("na") && strTgtCurrSwLevelMin.contains("na"))) {	// [10222020]
					objSiteInfo.isecmcapable = false;
				}
				
				// by now you should have all the info.
				// add to the csv arraylist (if not already added)
				
				if(!lstNodesAlreadyCaptured.contains(strNodeNameFoSwInfoDb)) {
					lstNodesAlreadyCaptured.add(strNodeNameFoSwInfoDb);
					csvArrayList.add(strNodeNameFoSwInfoDb + "," + "T-Mobile" + "," + SystemConstants.userSignum.toLowerCase() + "," + dateTimeForCsv + "," + strTgtCurrSwLevelMaj + "," + strTgtCurrSwLevelMin + "," + EAMSId + "," + objSiteInfo.isecmcapable);
				}
			}
		}
		catch (Exception ex) {
			blnNewSwInfoLogicHasError = true;
			GmoNotificationUtil.recordException(ex, "Exception while trying to generate SwInfoNew.csv", "shivdas.nair@ericsson.com");
		}

		try {
			if (!blnNewSwInfoLogicHasError) {
				if (csvArrayList.size() > 0) {
					FileUtil.writeDataToCsvFile(csvArrayList, FileUtil.getCmCiqDirectory() + File.separator + "SWinfoNew.csv");
				}
			}
		}
		catch(Exception ex) {
			// do nothing... non-critical feature.
		}
	}

	/**
	 * Function to generate NR 600 Market Specific script for CPA/Philly
	 * @param duInfo
	 * @param caDir
	 */
	public void generateNR600CPAScript(SiteCellObj duInfo, String caDirScript) {
		try {
			if (duInfo.tmoDUInfo.isNR600CarrierAddPhilly) {
				tmoCCR.generateNR600CPAScript(duInfo, caDirScript, "DOS");
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateNR600CPAScript exception!", e);
			Logger.getGmoLogger().printError("Error generating NR 600 Market Specific script for CPA/Philly Script! " + e.getMessage());
		}
	}
	
	public void generateRBSSummary() {

		try {
			String rbsSummary="";
			String integrationDirForEESI ="";
			String siteDirForEESI = "";
			String siteBBLSCSOWDirForEESI = "";
			String siteDirForEESIRollback = "";		// [06302020]
			String siteAutoBot = "";

			for (Entry<String, SiteCellObj> siteEntry : tmoCCR.getDUToDUInfo().entrySet()) {
				SiteCellObj duInfo = siteEntry.getValue();
				String site = siteEntry.getKey();
				if(!duInfo.isNewSite|| duInfo.has2GAnd3GSites) continue;
				String upGradePackageName = duInfo.pciSiteObj.release;	// [06022020] This is now stored for MMBB from kget, not CMCIQ. Calculated from upgradePackageId 
				if("".equalsIgnoreCase(upGradePackageName)) {
					Logger.logger.error("upgrade package is missing exception!");
					Logger.getGmoLogger().printError("upgrade package is missing exception!");
					return;
				}
				integrationDirForEESI = FileUtil.createDirReturnStr(outputDir + File.separator + "Integration");
				siteDirForEESI = FileUtil.createDirReturnStr(integrationDirForEESI + File.separator + "ESI_Input" + File.separator + site + File.separator + site);
				siteBBLSCSOWDirForEESI = FileUtil.createDirReturnStr(siteDirForEESI + File.separator + "Mobile_BBNSB_" + upGradePackageName);
				try {
					DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
					DocumentBuilder builder;
					DOMImplementation impl;
					builder = factory.newDocumentBuilder();
					impl = builder.getDOMImplementation();
					Document doc = impl.createDocument("", "summary:AutoIntegrationRbsSummaryFile", null);
					Element summary = doc.getDocumentElement();
					summary.setAttribute("xmlns:summary", "http://www.ericsson.se/RbsSummaryFileSchema");
					summary.setAttribute("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance");
					summary.setAttribute("xsi:schemaLocation", "http://www.ericsson.se/RbsSummaryFileSchemaSummaryFile.xsd");
					Element formatElement = doc.createElement("Format");
					formatElement.setAttribute("revision", "F");
					Element configurationFiles = doc.createElement("ConfigurationFiles");
					configurationFiles.setAttribute("initialSecurityConfigurationFilePath", duInfo.pciSiteObj.getOssNodeProtocolFile());
					configurationFiles.setAttribute("siteBasicFilePath", duInfo.pciSiteObj.SiteBasicTemplateName);
					configurationFiles.setAttribute("siteEquipmentFilePath", duInfo.pciSiteObj.SiteEquipmentTemplateName);
					configurationFiles.setAttribute("upgradePackageFilePath","Baseband_Radio_Node_" + duInfo.pciSiteObj.upgradePackageId.replaceAll("[-_/\\s]", "_"));
					configurationFiles.setAttribute("licensingKeyFilePath", !"".equalsIgnoreCase(duInfo.pciSiteObj.getLkfFilename()) ? duInfo.pciSiteObj.getLkfFilename() : "%EMPTY%");
					summary.appendChild(formatElement);
					summary.appendChild(configurationFiles);
					rbsSummary = xmlDOMToString(doc);
					File rbsSummaryFile = new File(siteBBLSCSOWDirForEESI+ File.separator + site + "_RbsSummary_file.xml");
					BufferedWriter bw = null;
					bw = new BufferedWriter(new FileWriter(rbsSummaryFile));
					bw.write(rbsSummary);
					if (bw != null) {
						bw.close();
					}

				}
				catch (Exception e) {
					Logger.logger.error("generateRBSSummary exception! duName=" + duInfo.duName, e);
					Logger.getGmoLogger().printError("Error generating RBS Summary file for " + duInfo.duName + "!");
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateRBSSummary exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating RBSSummary!");
		}
	
	}
	
	
	public void generate2gRBSSummary() {

		try {
			String rbsSummary="";
			for (Entry<String, SiteCellObj> siteEntry : tmoCCR.getDUToDUInfo().entrySet()) {
				SiteCellObj duInfo = siteEntry.getValue();
				String site = siteEntry.getKey();
				if(!duInfo.isNewSite|| !duInfo.has2GAnd3GSites) continue;
				String upGradePackageName = duInfo.pciSiteObj.release;	// [06022020] This is now stored for MMBB from kget, not CMCIQ. Calculated from upgradePackageId 
				if("".equalsIgnoreCase(upGradePackageName)) {
					Logger.logger.error("upgrade package is missing exception!");
					Logger.getGmoLogger().printError("upgrade package is missing exception!");
					return;
				}
				try {
					DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
					DocumentBuilder builder;
					DOMImplementation impl;
					builder = factory.newDocumentBuilder();
					impl = builder.getDOMImplementation();
					Document doc = impl.createDocument("", "summary:AutoIntegrationRbsSummaryFile", null);
					Element summary = doc.getDocumentElement();
					summary.setAttribute("xmlns:summary", "http://www.ericsson.se/RbsSummaryFileSchema");
					summary.setAttribute("xmlns:xsi", "http://www.w3.org/2001/XMLSchema-instance");
					summary.setAttribute("xsi:schemaLocation", "http://www.ericsson.se/RbsSummaryFileSchemaSummaryFile.xsd");
					Element formatElement = doc.createElement("Format");
					formatElement.setAttribute("revision", "F");
					Element configurationFiles = doc.createElement("ConfigurationFiles");
					configurationFiles.setAttribute("initialSecurityConfigurationFilePath", duInfo.pciSiteObj.getOssNodeProtocolFile());
					configurationFiles.setAttribute("siteBasicFilePath", "SiteBasic.xml");
					configurationFiles.setAttribute("siteEquipmentFilePath", "SiteEquipment_" + site + ".xml");
					configurationFiles.setAttribute("upgradePackageFilePath","Baseband_Radio_Node_" + duInfo.pciSiteObj.upgradePackageId.replaceAll("[-_/\\s]", "_"));
					configurationFiles.setAttribute("licensingKeyFilePath", !"".equalsIgnoreCase(duInfo.pciSiteObj.getLkfFilename()) ? duInfo.pciSiteObj.getLkfFilename() : "%EMPTY%");
					summary.appendChild(formatElement);
					summary.appendChild(configurationFiles);
					rbsSummary = xmlDOMToString(doc);
					String esi_path = outputDir + File.separator + "Integration" + File.separator + "ESI_Input" + File.separator + duInfo.gsm2G.cellList.get(0).nodeName + File.separator + duInfo.gsm2G.cellList.get(0).nodeName ;
					esi_path=esi_path + File.separator + "Mobile_BBNSB_" + upGradePackageName;
					File rbsSummaryFile = new File(esi_path + File.separator + duInfo.gsm2G.cellList.get(0).nodeName + "_RbsSummary_file.xml");
					BufferedWriter bw = null;
					bw = new BufferedWriter(new FileWriter(rbsSummaryFile));
					bw.write(rbsSummary);
					if (bw != null) {
						bw.close();
					}

				}
				catch (Exception e) {
					Logger.logger.error("generateRBSSummary exception! duName=" + duInfo.duName, e);
					Logger.getGmoLogger().printError("Error generating RBS Summary file for " + duInfo.duName + "!");
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateRBSSummary exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating RBSSummary!");
		}
	
	}
	
	
	protected String xmlDOMToString(Document doc) throws COException {
		Logger.logger.warn("Method: xmlDOMToString entered");
		StringWriter buffer = new StringWriter();
		try {
			TransformerFactory transFactory = TransformerFactory.newInstance();
			transFactory.setFeature(XMLConstants.FEATURE_SECURE_PROCESSING, true);
			Transformer transformer = transFactory.newTransformer();

			transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION, "yes");
			transformer.setOutputProperty(OutputKeys.INDENT, "yes");
			transformer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "4");
			Element root = doc.getDocumentElement();
			transformer.transform(new DOMSource(root), new StreamResult(buffer));
		} catch (Exception ex) {
			Logger.logger.warn("Method: xmlDOMToString, Exception: " + ex.getMessage());
			Logger.getGmoLogger().printWarning("Method: xmlDOMToString, Exception: " + ex.getMessage());			
			throw new COException("Method: xmlDOMToString, Exception: " + ex.getMessage());
		}
		return buffer.toString();
	}
	
	
	/** Refactored to FileUtil
	 * @deprecated
	 * @param input
	 * @param files
	 */
	protected void addfiles(File input, ArrayList<File> files) {
		if (input.isDirectory()) {
			ArrayList<File> path = new ArrayList<File>(Arrays.asList(input.listFiles()));
			for (int i = 0; i < path.size(); ++i) {
				if (path.get(i).isDirectory()) {
					addfiles(path.get(i), files);
				}
				if (path.get(i).isFile()) {
					files.add(path.get(i));
				}
			}
		}
		if (input.isFile()) {
			files.add(input);
		}
	}

	public GmoExecuter getGmoExecuter()
	{
		return gmoExecuter;
	}

	public void setGmoExecuter(GmoExecuter gmoExecuter)
	{
		this.gmoExecuter = gmoExecuter;
	}
	
	public void setScope(boolean scope)
	{
		this.isMDUScope = scope;
	}
	
	public boolean getScope()
	{
		return isMDUScope;
	}
	
	public boolean isIgnoreValidationDialog() {
		return ignoreValidationDialog;
	}

	public void setIgnoreValidationDialog(boolean ignoreValidationDialog) {
		this.ignoreValidationDialog = ignoreValidationDialog;
	}

	public TMODataCollector getTmoDC() {
		return tmoDC;
	}
	
	public TMO_Config_Change_Recorder getTMOCCR()
	{
		return tmoCCR;
	}

	public void setTmoCCR(TMO_Config_Change_Recorder tmoCCR)
	{
		this.tmoCCR = tmoCCR;
	}
	public TmoFileRenamingForESI getTmoFileRenamingForESI()	{
		return tmoFileRenamingForESI;
	}

	public void setTmoFileRenamingForESI(TmoFileRenamingForESI tmoFileRenamingForESI)
	{
		this.tmoFileRenamingForESI = tmoFileRenamingForESI;
	}
	
	public String getInputDir() {
		return inputDir;
	}
	
	public String getSiteList() {
		return siteList;
	}
	
	public String getOutputDir() {
		return outputDir;
	}
	
	public Set<String> getListOfSites() {
		return this.sites;
	}

	public Set<String> getSites() {
		return sites;
	}

	public void setSites(Set<String> sites) {
		this.sites = sites;
	}

	/**
	 * Function to generate SiteBasic for IPSec, separated to reduce complexity of updates
	 * @param duInfo
	 * @param file
	 * @param eolType
	 */
	private void generate5GNR600SiteBasicNetConf_MTR1923_IPSec(SiteCellObj duInfo, String file, String eolType)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		TMOIPSecScripts tmoIPSecScripts = new TMOIPSecScripts();
		tmoIPSecScripts.generate5GNR600SiteBasicNetConf(duInfo, file, eol);
	}

	/**
	 * Function to generate TN for IPSec, separated to reduce complexity of updates
	 * @param duInfo
	 * @param file
	 * @param eolType
	 */
	private void generateTNL19Q1IPSec(SiteCellObj duInfo, String file, String eolType, boolean adjustManagedElementId)
	{
		String eol = StringUtil.getEOL(eolType);
		Logger.getGmoLogger().printTextWithTimeStamp("creating " + file);
		TMOIPSecScripts tmoIPSecScripts = new TMOIPSecScripts();
		tmoIPSecScripts.generateTNL19Q1(duInfo, file, eol, duInfo.isBBU ? true : false);
	}
	
	public boolean getHasExcalibur4G5G() {
		return this.hasExcalibur4G5G;
	}
	
	public boolean getHas2GAnd3GSites(){
		return this.has2GAnd3GSites;
	}
	
	public boolean getgenerateExcalibur() {
		return this.generateExcalibur;
	}
	
	public boolean getHasDataPortMismatchSites(){
		return this.hasDataPortMismatchSites;
	}

	/**
	 * Function to generate N41 consolidation scripts
	 * GMO_TMO-200 NR41 Delta Sector Add + Parameter Preservation (N41 Node Consolidation)
	 * @param duInfo
	 * @param caDir
	 * @param site
	 */
	private void generateN41ConsolidationScripts(String site, String caDir, SiteCellObj duInfo) {
		try {
			if (duInfo.tmoDUInfo.trigger4SectorN41NodeConsolidation && duInfo.tmoDUInfo.movingCellsArraySiteGroup!=null && duInfo.tmoDUInfo.movingCellsArraySiteGroup.size()>0) {
				generateCarrierAdd01Script(duInfo, caDir + File.separator + "00_" + duInfo.duName + "_CarrierAdd_N41.mos", "DOS");
				// parameter preservation script
				ParamPreservation pp = new ParamPreservation();
				pp.setSite(site);
				pp.setSoftwareLevel(duInfo.softwareLevel);
				pp.setBBU(duInfo.isBBU);
				pp.setInputFormat(duInfo.inputFormat);
				pp.setOutputFormat(duInfo.outputFormat);
				pp.setMarket(duInfo.getSiteObj().getMarket());
				pp.setTmoCCR(tmoCCR);
				pp.initializeGeneric();
				tmoCCR.generateMixedModeBaseBandNR600ParameterPreservationScript(duInfo, duInfo.duName, caDir + File.separator + "01a_" + duInfo.duName + "_Node_parameter_change.mos", pp);
				SiteCellObj duInfoToDelete = tmoDC.getDeletedDuInfoForDu(sites);
				if (duInfoToDelete != null && duInfoToDelete.isRemovedDU) {
					String apDeleteScriptsDir = FileUtil.createDirReturnStr(caDir + File.separator + duInfoToDelete.duNameOld);
					String apDeleteENMScriptFile = apDeleteScriptsDir + File.separator + duInfoToDelete.duNameOld + "_Node_Delete_ENM.mos";
					tmoCCR.generateAPDeleteENMScript(duInfoToDelete.duName, apDeleteENMScriptFile);
				}
			}
		}
		catch (Exception e) {
			Logger.logger.error("generateN41ConsolidationScripts exception!", e);
			Logger.getGmoLogger().printTextWithTimeStamp("Error generating N41 Consolidation Scripts!");
		}
	}
}
