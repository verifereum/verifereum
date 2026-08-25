Theory vfmTest1976[no_sig_docs]
Ancestors vfmTestDefs1976
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1976_0.nsv", "result1976_1.nsv", "result1976_2.nsv", "result1976_3.nsv", "result1976_4.nsv", "result1976_5.nsv", "result1976_6.nsv", "result1976_7.nsv", "result1976_8.nsv", "result1976_9.nsv", "result1976_10.nsv", "result1976_11.nsv", "result1976_12.nsv", "result1976_13.nsv", "result1976_14.nsv", "result1976_15.nsv", "result1976_16.nsv", "result1976_17.nsv", "result1976_18.nsv", "result1976_19.nsv"];
val thyn = "vfmTestDefs1976";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
