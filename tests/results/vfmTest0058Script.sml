Theory vfmTest0058[no_sig_docs]
Ancestors vfmTestDefs0058
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0058_0.nsv", "result0058_1.nsv", "result0058_2.nsv", "result0058_3.nsv", "result0058_4.nsv", "result0058_5.nsv", "result0058_6.nsv", "result0058_7.nsv", "result0058_8.nsv", "result0058_9.nsv", "result0058_10.nsv", "result0058_11.nsv", "result0058_12.nsv", "result0058_13.nsv", "result0058_14.nsv", "result0058_15.nsv", "result0058_16.nsv", "result0058_17.nsv", "result0058_18.nsv", "result0058_19.nsv", "result0058_20.nsv", "result0058_21.nsv", "result0058_22.nsv", "result0058_23.nsv"];
val thyn = "vfmTestDefs0058";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
