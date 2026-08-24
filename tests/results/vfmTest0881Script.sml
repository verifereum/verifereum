Theory vfmTest0881[no_sig_docs]
Ancestors vfmTestDefs0881
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0881_0.nsv", "result0881_1.nsv", "result0881_2.nsv"];
val thyn = "vfmTestDefs0881";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
