Theory vfmTest0995[no_sig_docs]
Ancestors vfmTestDefs0995
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0995_0.nsv", "result0995_1.nsv", "result0995_2.nsv", "result0995_3.nsv"];
val thyn = "vfmTestDefs0995";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
