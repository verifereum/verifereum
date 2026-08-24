Theory vfmTest0077[no_sig_docs]
Ancestors vfmTestDefs0077
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0077_0.nsv", "result0077_1.nsv", "result0077_2.nsv"];
val thyn = "vfmTestDefs0077";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
