Theory vfmTest2966[no_sig_docs]
Ancestors vfmTestDefs2966
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2966_0.nsv", "result2966_1.nsv", "result2966_2.nsv", "result2966_3.nsv", "result2966_4.nsv", "result2966_5.nsv", "result2966_6.nsv", "result2966_7.nsv"];
val thyn = "vfmTestDefs2966";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
