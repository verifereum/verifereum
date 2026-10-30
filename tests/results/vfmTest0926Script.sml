Theory vfmTest0926[no_sig_docs]
Ancestors vfmTestDefs0926
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0926_0.nsv", "result0926_1.nsv", "result0926_2.nsv", "result0926_3.nsv", "result0926_4.nsv", "result0926_5.nsv"];
val thyn = "vfmTestDefs0926";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
