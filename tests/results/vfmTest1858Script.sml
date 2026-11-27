Theory vfmTest1858[no_sig_docs]
Ancestors vfmTestDefs1858
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1858_0.nsv", "result1858_1.nsv", "result1858_2.nsv", "result1858_3.nsv", "result1858_4.nsv", "result1858_5.nsv", "result1858_6.nsv", "result1858_7.nsv", "result1858_8.nsv", "result1858_9.nsv", "result1858_10.nsv", "result1858_11.nsv", "result1858_12.nsv", "result1858_13.nsv", "result1858_14.nsv", "result1858_15.nsv", "result1858_16.nsv", "result1858_17.nsv", "result1858_18.nsv", "result1858_19.nsv"];
val thyn = "vfmTestDefs1858";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
