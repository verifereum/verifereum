Theory vfmTest1965[no_sig_docs]
Ancestors vfmTestDefs1965
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1965_0.nsv", "result1965_1.nsv", "result1965_2.nsv", "result1965_3.nsv", "result1965_4.nsv", "result1965_5.nsv", "result1965_6.nsv", "result1965_7.nsv", "result1965_8.nsv", "result1965_9.nsv", "result1965_10.nsv", "result1965_11.nsv", "result1965_12.nsv", "result1965_13.nsv", "result1965_14.nsv", "result1965_15.nsv", "result1965_16.nsv", "result1965_17.nsv"];
val thyn = "vfmTestDefs1965";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
