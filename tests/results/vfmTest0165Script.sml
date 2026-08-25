Theory vfmTest0165[no_sig_docs]
Ancestors vfmTestDefs0165
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0165_0.nsv", "result0165_1.nsv", "result0165_2.nsv", "result0165_3.nsv"];
val thyn = "vfmTestDefs0165";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
