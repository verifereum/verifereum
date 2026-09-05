Theory vfmTest2217[no_sig_docs]
Ancestors vfmTestDefs2217
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2217_0.nsv", "result2217_1.nsv", "result2217_2.nsv", "result2217_3.nsv", "result2217_4.nsv"];
val thyn = "vfmTestDefs2217";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
