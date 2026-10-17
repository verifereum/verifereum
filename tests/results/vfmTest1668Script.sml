Theory vfmTest1668[no_sig_docs]
Ancestors vfmTestDefs1668
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1668_0.nsv", "result1668_1.nsv", "result1668_2.nsv", "result1668_3.nsv", "result1668_4.nsv", "result1668_5.nsv", "result1668_6.nsv", "result1668_7.nsv", "result1668_8.nsv", "result1668_9.nsv", "result1668_10.nsv", "result1668_11.nsv", "result1668_12.nsv", "result1668_13.nsv", "result1668_14.nsv", "result1668_15.nsv", "result1668_16.nsv", "result1668_17.nsv", "result1668_18.nsv", "result1668_19.nsv"];
val thyn = "vfmTestDefs1668";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
