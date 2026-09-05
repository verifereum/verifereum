Theory vfmTest0185[no_sig_docs]
Ancestors vfmTestDefs0185
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0185_0.nsv", "result0185_1.nsv", "result0185_2.nsv", "result0185_3.nsv"];
val thyn = "vfmTestDefs0185";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
