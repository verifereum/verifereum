Theory vfmTest0186[no_sig_docs]
Ancestors vfmTestDefs0186
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0186_0.nsv", "result0186_1.nsv", "result0186_2.nsv", "result0186_3.nsv"];
val thyn = "vfmTestDefs0186";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
