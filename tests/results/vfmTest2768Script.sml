Theory vfmTest2768[no_sig_docs]
Ancestors vfmTestDefs2768
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2768_0.nsv", "result2768_1.nsv", "result2768_2.nsv", "result2768_3.nsv"];
val thyn = "vfmTestDefs2768";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
