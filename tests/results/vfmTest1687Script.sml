Theory vfmTest1687[no_sig_docs]
Ancestors vfmTestDefs1687
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1687_0.nsv", "result1687_1.nsv", "result1687_2.nsv", "result1687_3.nsv", "result1687_4.nsv", "result1687_5.nsv", "result1687_6.nsv", "result1687_7.nsv", "result1687_8.nsv", "result1687_9.nsv", "result1687_10.nsv", "result1687_11.nsv", "result1687_12.nsv", "result1687_13.nsv", "result1687_14.nsv", "result1687_15.nsv", "result1687_16.nsv", "result1687_17.nsv", "result1687_18.nsv", "result1687_19.nsv"];
val thyn = "vfmTestDefs1687";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
