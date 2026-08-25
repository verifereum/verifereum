Theory vfmTest0222[no_sig_docs]
Ancestors vfmTestDefs0222
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0222_0.nsv", "result0222_1.nsv"];
val thyn = "vfmTestDefs0222";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
