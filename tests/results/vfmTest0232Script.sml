Theory vfmTest0232[no_sig_docs]
Ancestors vfmTestDefs0232
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0232_0.nsv", "result0232_1.nsv", "result0232_2.nsv"];
val thyn = "vfmTestDefs0232";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
