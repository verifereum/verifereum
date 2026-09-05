Theory vfmTest0455[no_sig_docs]
Ancestors vfmTestDefs0455
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0455_0.nsv", "result0455_1.nsv"];
val thyn = "vfmTestDefs0455";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
