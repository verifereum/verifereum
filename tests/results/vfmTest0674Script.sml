Theory vfmTest0674[no_sig_docs]
Ancestors vfmTestDefs0674
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0674_0.nsv", "result0674_1.nsv", "result0674_2.nsv", "result0674_3.nsv"];
val thyn = "vfmTestDefs0674";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
