Theory vfmTest2764[no_sig_docs]
Ancestors vfmTestDefs2764
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2764_0.nsv", "result2764_1.nsv", "result2764_2.nsv", "result2764_3.nsv"];
val thyn = "vfmTestDefs2764";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
