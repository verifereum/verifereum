Theory vfmTest0689[no_sig_docs]
Ancestors vfmTestDefs0689
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0689_0.nsv", "result0689_1.nsv", "result0689_2.nsv", "result0689_3.nsv", "result0689_4.nsv", "result0689_5.nsv"];
val thyn = "vfmTestDefs0689";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
