Theory vfmTest2074[no_sig_docs]
Ancestors vfmTestDefs2074
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2074_0.nsv", "result2074_1.nsv", "result2074_2.nsv", "result2074_3.nsv", "result2074_4.nsv", "result2074_5.nsv", "result2074_6.nsv", "result2074_7.nsv", "result2074_8.nsv", "result2074_9.nsv", "result2074_10.nsv", "result2074_11.nsv", "result2074_12.nsv", "result2074_13.nsv", "result2074_14.nsv", "result2074_15.nsv"];
val thyn = "vfmTestDefs2074";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
