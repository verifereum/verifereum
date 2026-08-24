Theory vfmTest0468[no_sig_docs]
Ancestors vfmTestDefs0468
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0468_0.nsv", "result0468_1.nsv", "result0468_2.nsv", "result0468_3.nsv", "result0468_4.nsv"];
val thyn = "vfmTestDefs0468";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
