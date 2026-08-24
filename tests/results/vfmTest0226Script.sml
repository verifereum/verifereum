Theory vfmTest0226[no_sig_docs]
Ancestors vfmTestDefs0226
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0226_0.nsv", "result0226_1.nsv", "result0226_2.nsv", "result0226_3.nsv", "result0226_4.nsv"];
val thyn = "vfmTestDefs0226";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
