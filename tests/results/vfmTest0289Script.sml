Theory vfmTest0289[no_sig_docs]
Ancestors vfmTestDefs0289
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0289_0.nsv", "result0289_1.nsv"];
val thyn = "vfmTestDefs0289";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
