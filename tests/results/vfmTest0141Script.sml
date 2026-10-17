Theory vfmTest0141[no_sig_docs]
Ancestors vfmTestDefs0141
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0141_0.nsv", "result0141_1.nsv"];
val thyn = "vfmTestDefs0141";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
