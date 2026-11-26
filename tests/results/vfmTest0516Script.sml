Theory vfmTest0516[no_sig_docs]
Ancestors vfmTestDefs0516
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0516_0.nsv", "result0516_1.nsv"];
val thyn = "vfmTestDefs0516";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
