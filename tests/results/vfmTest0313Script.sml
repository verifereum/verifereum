Theory vfmTest0313[no_sig_docs]
Ancestors vfmTestDefs0313
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0313_0.nsv", "result0313_1.nsv", "result0313_2.nsv"];
val thyn = "vfmTestDefs0313";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
