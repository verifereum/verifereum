Theory vfmTest1536[no_sig_docs]
Ancestors vfmTestDefs1536
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1536_0.nsv", "result1536_1.nsv", "result1536_2.nsv", "result1536_3.nsv", "result1536_4.nsv", "result1536_5.nsv", "result1536_6.nsv", "result1536_7.nsv", "result1536_8.nsv", "result1536_9.nsv", "result1536_10.nsv", "result1536_11.nsv", "result1536_12.nsv", "result1536_13.nsv", "result1536_14.nsv", "result1536_15.nsv", "result1536_16.nsv", "result1536_17.nsv", "result1536_18.nsv", "result1536_19.nsv"];
val thyn = "vfmTestDefs1536";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
