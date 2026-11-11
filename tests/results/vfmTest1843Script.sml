Theory vfmTest1843[no_sig_docs]
Ancestors vfmTestDefs1843
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1843_0.nsv", "result1843_1.nsv", "result1843_2.nsv", "result1843_3.nsv", "result1843_4.nsv", "result1843_5.nsv", "result1843_6.nsv", "result1843_7.nsv", "result1843_8.nsv", "result1843_9.nsv", "result1843_10.nsv", "result1843_11.nsv", "result1843_12.nsv", "result1843_13.nsv", "result1843_14.nsv", "result1843_15.nsv", "result1843_16.nsv", "result1843_17.nsv", "result1843_18.nsv", "result1843_19.nsv"];
val thyn = "vfmTestDefs1843";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
