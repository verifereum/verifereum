Theory vfmTest0115[no_sig_docs]
Ancestors vfmTestDefs0115
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0115_0.nsv", "result0115_1.nsv"];
val thyn = "vfmTestDefs0115";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
