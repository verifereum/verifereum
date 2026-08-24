Theory vfmTest0607[no_sig_docs]
Ancestors vfmTestDefs0607
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0607_0.nsv"];
val thyn = "vfmTestDefs0607";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
