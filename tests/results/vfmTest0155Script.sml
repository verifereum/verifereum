Theory vfmTest0155[no_sig_docs]
Ancestors vfmTestDefs0155
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0155_0.nsv", "result0155_1.nsv"];
val thyn = "vfmTestDefs0155";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
