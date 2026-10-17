Theory vfmTest2219[no_sig_docs]
Ancestors vfmTestDefs2219
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2219_0.nsv", "result2219_1.nsv", "result2219_2.nsv", "result2219_3.nsv", "result2219_4.nsv", "result2219_5.nsv"];
val thyn = "vfmTestDefs2219";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
